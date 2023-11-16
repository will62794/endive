---- MODULE AbstractRaft ----
\*
\* High level specification of Raft protocol without dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Apalache


CONSTANTS 
    \* @typeAlias: SERVER = Str;
    \* @type: Set(SERVER);
    Server

CONSTANTS 
    \* @type: Str;
    Secondary, 
    \* @type: Str;
    Primary, 
    \* @type: Str;
    Nil

CONSTANT
    \* @type: Int; 
    InitTerm

VARIABLE 
    \* @type: SERVER -> Int; 
    currentTerm

VARIABLE 
    \* @type: SERVER -> Str;
    state

VARIABLE 
    \* @type: SERVER -> Seq(Int);
    log

VARIABLE
   \* @type: Set( <<Int, Int>> );
    immediatelyCommitted

vars == <<currentTerm, state, log, immediatelyCommitted>>

\*
\* Helper operators.
\*

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
\* @type: (<<Int,Int>>,SERVER) => Bool;
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* @type: Seq(Int) => <<Int, Int>>;
LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

\* @type: (Seq(Int), Int) => Int;
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* The set of all quorums in a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately committed in term 't' with a quorum 'Q'.
\* @type: (<<Int, Int>>, Set(SERVER)) => Bool;
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, immediatelyCommitted>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<immediatelyCommitted, currentTerm, state>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ state[i] = Secondary
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<immediatelyCommitted, currentTerm, state>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ UNCHANGED <<log, immediatelyCommitted>>   
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in immediatelyCommitted : c[1] = ind /\ c[2] = currentTerm[i] 
    \* /\ committed' = committed \cup {<<ind, currentTerm[i], currentTerm[i]>>}
    /\ immediatelyCommitted' = immediatelyCommitted \cup {<<ind, currentTerm[i]>>}
    /\ UNCHANGED <<currentTerm, state, log>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, immediatelyCommitted>>

Init == 
    /\ currentTerm = [i \in Server |-> InitTerm]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ immediatelyCommitted = {}

\* Add dummy precondition for now so TLC tags actions by name explicitly.
ClientRequestAction == TRUE /\ \E s \in Server : ClientRequest(s)
GetEntriesAction == TRUE /\ \E s, t \in Server : GetEntries(s, t)
RollbackEntriesAction == TRUE /\ \E s, t \in Server : RollbackEntries(s, t)
BecomeLeaderAction == TRUE /\ \E s \in Server : \E Q \in Quorums(Server) : BecomeLeader(s, Q)
CommitEntryAction ==  TRUE /\ \E s \in Server :  \E Q \in Quorums(Server) : CommitEntry(s, Q)
UpdateTermsAction == TRUE /\ \E s,t \in Server : UpdateTerms(s, t)

Next == 
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntriesAction
    \/ BecomeLeaderAction
    \/ CommitEntryAction
    \/ UpdateTermsAction

NextUnchanged == UNCHANGED vars

--------------------------------------------------------------------------------


CONSTANTS 
    \* @type: Int;
    MaxTerm, 
    \* @type: Int;
    MaxLogLen

\* State Constraint. Used for model checking only.
StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

Symmetry == Permutations(Server)

Terms == InitTerm..MaxTerm
LogIndices == 1..MaxLogLen

\* CServerInit == {"s1", "s2", "s3"}
\* CServerInitSize == 3

CServerInit == {"s1", "s2", "s3", "s4"}
CServerInitSize == 4

CInit == 
    /\ Primary = "Primary"
    /\ Secondary = "Secondary"
    /\ Nil = "Nil"
    /\ Server = CServerInit
    /\ MaxLogLen = 3
    /\ MaxTerm = 3
    /\ InitTerm = 0

\* Statement of type correctness tailored to Apalache. 
ApaTypeOK ==
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Secondary, Primary}]
    \* Size of log generator should be at least as large as number of
    \* servers and max length of logs.
    /\ log = Gen(CServerInitSize)
    /\ \A s \in Server : \A i \in DOMAIN log[s] : log[s][i] \in Terms
    /\ \A s \in Server : Len(log[s]) <= MaxLogLen
    /\ DOMAIN log = Server
    \* I believe this should constraint 'committed' to be a set of size 3,
    \* with elements of the appropriate type.
    /\ immediatelyCommitted = Gen(3)
    /\ \A c \in immediatelyCommitted : c \in (LogIndices \X Terms)

\* 
\* Helper lemmas.
\* 

\* START_PROOF

\*
\* Correctness properties
\*

H_OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

LeaderAppendOnly == 
    [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

\* <<index, term>> pairs uniquely identify log prefixes.
H_LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries committed in previous terms.
H_LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in immediatelyCommitted : (c[2] < currentTerm[s] => InLog(<<c[1],c[2]>>, s))

\* \* If two entries are committed at the same index, they must be the same entry.
H_StateMachineSafety == 
    \A c1, c2 \in immediatelyCommitted : (c1[1] = c2[1]) => (c1 = c2)


\* Dummy lemma that is trivially true.
H_TRUE == Cardinality(DOMAIN state) >= 0

\* If a primary has been elected at term T, then there must exist a quorum at term >= T.
H_QuorumsSafeAtTerms == 
    \A s \in Server : (state[s] = Primary) =>
        (\E Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= currentTerm[s])

H_TermsMonotonic ==
    \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])

H_PrimaryTermAtLeastAsLargeAsLogTerms == 
    \A s \in Server : (state[s] = Primary) => 
        \A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i]

H_CommittedEntryIsOnQuorum == 
    \A c \in immediatelyCommitted :
        \E Q \in Quorums(Server) : \A n \in Q : InLog(<<c[1],c[2]>>, n)  

H_CommittedEntryIsOnQuorum_cyclebreak == 
    \A c \in immediatelyCommitted :
        \E Q \in Quorums(Server) : \A n \in Q : InLog(<<c[1],c[2]>>, n)

H_EntriesCommittedInOwnOrLaterTerm == 
    \* \A c \in committed : c[3] >= c[2] 
    \A c \in immediatelyCommitted : c[2] >= c[2] 

H_EntriesCommittedInOwnTerm == 
    \* \A c \in committed : c[3] = c[2] 
    \A c \in immediatelyCommitted : c[2] = c[2] 

\* Existence of an entry in term T implies a past election in T, so 
\* there must be some quorum at this term or greater.
H_LogEntryImpliesSafeAtTerm == 
    \A s \in Server : 
    \A i \in DOMAIN log[s] :
        \E Q \in Quorums(Server) : \A n \in Q : currentTerm[n] >= log[s][i]

\* If a server's latest log term exceeds a committed entry c's term, then it must contain that 
\* committed entry in its log.
H_LaterLogsHaveEarlierCommitted ==
    \A s \in Server : 
    \A c \in immediatelyCommitted :
        \* Exists an entry in log[s] with a term greater than the term in which the entry was committed.
        (\E i \in DOMAIN log[s] : (log[s][i] > c[2])) =>
            /\ Len(log[s]) >= c[1]
            /\ log[s][c[1]] = c[2] \* entry exists in the server's log.

\* Alternate statement of the above that I think works just as well.
H_LaterLogsMustHaveCommittedAlt ==
    \A s \in Server : 
    \A c \in immediatelyCommitted :
        \* Exists an entry in log[s] with a term greater than the term in which the entry was committed.
        (LastTerm(log[s]) > c[2]) =>
            /\ Len(log[s]) >= c[1]
            /\ log[s][c[1]] = c[2] \* entry exists in the server's log.

\* If a server's latest log term exceeds a committed entry c's term, then it must contain that 
\* committed entry in its log. Also, primary logs must contain entries committed in earlier terms.
H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted ==
    /\ H_LaterLogsHaveEarlierCommitted
    /\ H_LeaderCompleteness

H_LogsWithEntryInTermMustHaveEarlierCommittedEntriesFromTerm ==
    \A s \in Server : 
    \A c \in immediatelyCommitted :
        \* Exists an entry with same term as the committed entry. 
        (\E i \in DOMAIN log[s] : log[s][i] = c[2] /\ i >= c[1]) =>
                    /\ Len(log[s]) >= c[1]
                    /\ log[s][c[1]] = c[2]

\* If a log entry exists in term T and there is a primary in term T, then this
\* log entry should be present in that primary's log.
H_PrimaryHasOwnEntries == 
    \A i,j \in Server :
    (state[i] = Primary) => 
    \* Can't be that another node has an entry in this primary's term
    \* but the primary doesn't have it.
        ~(\E k \in DOMAIN log[j] :
            /\ log[j][k] = currentTerm[i]
            /\ ~InLog(<<k,log[j][k]>>, i))

\* A server's current term is always at least as large as the terms in its log.
H_PrimaryTermGTELogTerm == 
    \A s \in Server : 
        (state[s] = Primary) => 
            (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* If a log contains an entry in term T at index I such that
\* the entries at J < I are in a different term, then there must be
\* no other logs that contains entries in term T at indices J < I
H_UniformLogEntries ==
    \A s,t \in Server :
    \A i \in DOMAIN log[s] : 
        (\A j \in DOMAIN log[s] : (j < i) => log[s][j] # log[s][i]) => 
            (~\E k \in DOMAIN log[t] : log[t][k] = log[s][i] /\ k < i)

\* H_CommittedEntryIsOnQuorum_AND_LogsLaterThanCommittedMustHaveCommitted_AND_LeaderCompleteness == 
\*     /\ LeaderCompleteness
\*     /\ H_CommittedEntryIsOnQuorum
\*     /\ H_LaterLogsMustHaveCommitted

H_UniformLogEntries_AND_TermsGrowMonotonically == 
    /\ H_UniformLogEntries
    /\ H_TermsMonotonic

H_CoreLogInv == H_UniformLogEntries_AND_TermsGrowMonotonically

\* Invariant developed during inductive proof decomposition experimenting.
\* 08/19/2023
HumanDecompInd == 
    /\ H_StateMachineSafety
    /\ H_LeaderCompleteness
    /\ H_CommittedEntryIsOnQuorum
    /\ H_LaterLogsHaveEarlierCommitted
    /\ H_PrimaryTermGTELogTerm
    /\ H_EntriesCommittedInOwnOrLaterTerm
    /\ H_EntriesCommittedInOwnTerm
    /\ H_LogEntryImpliesSafeAtTerm
    /\ H_OnePrimaryPerTerm
    /\ H_PrimaryHasOwnEntries
    /\ H_QuorumsSafeAtTerms
    /\ H_TermsMonotonic
    /\ H_LogMatching
    /\ H_UniformLogEntries

HumanDecompIndWithApaTypeOK ==
    /\ ApaTypeOK
    /\ HumanDecompInd   

HumanDecompInd_WithConstraint == StateConstraint => HumanDecompInd

=============================================================================
