--------------------------------- MODULE AsyncRaft ---------------------------------
(* NOTES 

Spec of Raft with message passing.

Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

This is a model checking optimized fork of original spec.

- Summary of changes:
    - updated message helpers:
        - prevent resending the same message multiple times (unless explicity via the duplicate action)
        - can only receive a message that hasn't been delivered yet
    - optimized for model checking (reduction in state space)
        - removed history variables (using simple invariants instead)
        - decomposed "receive" into separate actions
        - compressed multi-step append_entries_req processing into one.
        - compressed timeout and requestvote into single action
        - server directly votes for itself in an election (it doesn't send itself a vote request)
    - fixed some bugs
        - adding the same value over and over again
        - allowing actions to remain enabled producing odd results
    
Notes on action enablement.
 - Send is only enabled if the mesage has not been previously sent.
   This is leveraged to disable actions once executed, such as sending a specific 
   AppendEntrieRequest. It won't be sent again, so no need for extra variables to track that. 

Original source: https://github.com/Vanlightly/raft-tlaplus/blob/main/specifications/standard-raft/Raft.tla
Modified further by Will Schultz for safety proof experiments, August 2023.
*)

\* EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, Bags, TLC
EXTENDS Naturals, FiniteSets, Sequences, TLC
\* , Randomization

\* The set of server IDs
CONSTANTS 
    \* @typeAlias: SERVER = Str;
    \* @type: Set(SERVER);
    Server

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower, 
    \* @type: Str;
    Candidate, 
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Str;
    Nil

\* Message types:
CONSTANTS 
    \* @type: Str;
    RequestVoteRequest, 
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest, 
    \* @type: Str;
    AppendEntriesResponse

----
\* Global variables.

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: SERVER, mdest: SERVER });
    requestVoteRequestMsgs

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, mvoteGranted: Bool, msource: SERVER, mdest: SERVER });
    requestVoteResponseMsgs

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER });
    appendEntriesRequestMsgs

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: SERVER, mdest: SERVER });
    appendEntriesResponseMsgs

----
\* Auxilliary variables (used for state-space control, invariants etc)

\* The server's term number.
VARIABLE 
    \* @type: SERVER -> Int; 
    currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE 
    \* @type: SERVER -> Str; 
    state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE 
    \* @type: SERVER -> SERVER;
    votedFor

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE 
    \* @type: SERVER -> Seq(Int);
    log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: SERVER -> Int;
    commitIndex


\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: SERVER -> Set(SERVER);
    votesGranted


\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE
    \* @type: SERVER -> (SERVER -> Int);
    nextIndex

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: SERVER -> (SERVER -> Int);
    matchIndex


serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>

\* End of per server variables.-

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex>>

\* Helpers

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))
  
----
\* Define initial values for all variables

\* InitcurrentTerm, state, votedFor == /\ currentTerm = [i \in Server |-> 1]
\*                   /\ state       = [i \in Server |-> Follower]
\*                   /\ votedFor    = [i \in Server |-> Nil]
\* InitCandidateVars == votesGranted   = [i \in Server |-> {}]
\* \* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* \* leader does not send itself messages. It's still easier to include these
\* \* in the functions.
\* InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
\*                   /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
\* Initlog, commitIndex == /\ log             = [i \in Server |-> << >>]
\*                /\ commitIndex     = [i \in Server |-> 0]

Init == 
    /\ requestVoteRequestMsgs = {}
    /\ requestVoteResponseMsgs = {}
    /\ appendEntriesRequestMsgs = {}
    /\ appendEntriesResponseMsgs = {}
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Follower]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ votesGranted = [i \in Server |-> {}]
    /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]        
    /\ log             = [i \in Server |-> << >>]
    /\ commitIndex     = [i \in Server |-> 0]
    
----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor and log.
Restart(i) ==
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs, appendEntriesResponseMsgs>>

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ requestVoteRequestMsgs' = requestVoteRequestMsgs \cup 
            {[  mtype         |-> RequestVoteRequest,
                mterm         |-> currentTerm[i] + 1,
                mlastLogTerm  |-> LastTerm(log[i]),
                mlastLogIndex |-> Len(log[i]),
                msource       |-> i,
                mdest         |-> j] : j \in Server \ {i}}
    /\ UNCHANGED <<nextIndex, matchIndex, log, commitIndex, appendEntriesRequestMsgs, appendEntriesResponseMsgs, requestVoteResponseMsgs>>

\* ACTION: AppendEntries ----------------------------------------
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF (prevLogIndex > 0 /\ prevLogIndex \in DOMAIN log[i])
                            THEN log[i][prevLogIndex]
                            ELSE 0
           \* Send up to 1 entry, constrained by the end of the log.
           \* NOTE: This spec never sends more than one entry at a time currently. (Will S.)
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN 
          /\ appendEntriesRequestMsgs' = appendEntriesRequestMsgs \cup {[
                   mtype          |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                   mprevLogIndex  |-> prevLogIndex,
                   mprevLogTerm   |-> prevLogTerm,
                   mentries       |-> entries,
                   mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j]}
    /\ UNCHANGED <<currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesResponseMsgs>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, votedFor, votesGranted, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* The set of servers that agree up through index.
Agree(i, index) == {i} \cup {k \in Server : matchIndex[i][k] >= index }

\* ACTION: AdvanceCommitIndex ---------------------------------
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in DOMAIN log[i] : Agree(i, index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)] = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, requestVoteRequestMsgs, requestVoteResponseMsgs>>

UpdateTerm(mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>


\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTermRVReq(mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

UpdateTermRVRes(mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

UpdateTermAEReq(mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

UpdateTermAERes(mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>



\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: ({ mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
HandleRequestVoteRequest(m) ==
    /\ m \in requestVoteRequestMsgs
    /\ m.mtype = RequestVoteRequest
    /\ m.mterm <= currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                     \/ /\ m.mlastLogTerm = LastTerm(log[i])
                        /\ m.mlastLogIndex >= Len(log[i])
            grant == /\ m.mterm = currentTerm[i]
                     /\ logOk
                     /\ votedFor[i] \in {Nil, j} 
                     IN
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ requestVoteResponseMsgs' = requestVoteResponseMsgs \cup {[
                            mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            msource      |-> i,
                            mdest        |-> j]}
            /\ UNCHANGED <<state, currentTerm, votesGranted, nextIndex, matchIndex, log, commitIndex, appendEntriesRequestMsgs, appendEntriesResponseMsgs, requestVoteRequestMsgs>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m \in requestVoteResponseMsgs
    /\ m.mtype = RequestVoteResponse
    /\ m.mterm = currentTerm[m.mdest]
    /\ votesGranted' = [votesGranted EXCEPT ![m.mdest] = 
                                IF m.mvoteGranted 
                                    THEN votesGranted[m.mdest] \cup {m.msource} 
                                    ELSE votesGranted[m.mdest]]
    /\ requestVoteResponseMsgs' = requestVoteResponseMsgs \ {m} \* discard the message.
    /\ UNCHANGED <<currentTerm, state, votedFor, nextIndex, matchIndex, log, commitIndex, appendEntriesRequestMsgs, appendEntriesResponseMsgs, requestVoteRequestMsgs>>

\* ACTION: RejectAppendEntriesRequest -------------------
\* Either the term of the message is stale or the message
\* entry is too high (beyond the last log entry + 1)
\* @type: (SERVER, { mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
LogOk(i, m) ==
    \/ m.mprevLogIndex = 0
    \/ /\ m.mprevLogIndex > 0
       /\ m.mprevLogIndex <= Len(log[i])
       /\ m.mprevLogTerm = log[i][m.mprevLogIndex]


\* @type: ({ mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
RejectAppendEntriesRequest(m) ==
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm <= currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == LogOk(i, m)
        IN  /\ \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \cup 
                {[
                        mtype           |-> AppendEntriesResponse,
                        mterm           |-> currentTerm[i],
                        msuccess        |-> FALSE,
                        mmatchIndex     |-> 0,
                        msource         |-> i,
                        mdest           |-> j]}
            /\ UNCHANGED <<state, votesGranted, nextIndex, matchIndex, currentTerm, state, votedFor, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>

\* ACTION: AcceptAppendEntriesRequest ------------------
\* The original spec had to three sub actions, this version is compressed.
\* In one step it can:
\* - truncate the log
\* - append an entry to the log
\* - respond to the leader         
\* @type: ({ mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER }, SERVER) => Bool;
CanAppend(m, i) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    
\* truncate in two cases:
\* - the last log entry index is >= than the entry being received
\* - this is an empty RPC and the last log entry index is > than the previous log entry received
\* NeedsTruncation(m, i, index) ==
\*    \/ /\ m.mentries /= <<>>
\*       /\ Len(log[i]) >= index
\*    \/ /\ m.mentries = <<>>
\*       /\ Len(log[i]) > m.mprevLogIndex

\* TruncateLog(m, i) ==
\*     [index \in 1..m.mprevLogIndex |-> log[i][index]]

AcceptAppendEntriesRequestAppend(m) ==
    /\ m \in appendEntriesRequestMsgs
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm = currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == LogOk(i, m)
            index == m.mprevLogIndex + 1
        IN 
            /\ state[i] \in { Follower, Candidate }
            /\ logOk
            /\ CanAppend(m, i)
            /\ state' = [state EXCEPT ![i] = Follower]
            \* Only update the logs in this action. commit learning is done in a separate action.
            /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \cup {[
                        mtype           |-> AppendEntriesResponse,
                        mterm           |-> currentTerm[i],
                        msuccess        |-> TRUE,
                        mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                        msource         |-> i,
                        mdest           |-> j]}
            /\ UNCHANGED <<votesGranted, commitIndex, nextIndex, matchIndex, votedFor, currentTerm, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>
       
\* AcceptAppendEntriesRequestTruncate(m) ==
\*     /\ m \in appendEntriesRequestMsgs
\*     /\ m.mtype = AppendEntriesRequest
\*     /\ m.mterm = currentTerm[m.mdest]
\*     /\ LET  i     == m.mdest
\*             j     == m.msource
\*             logOk == LogOk(i, m)
\*             index == m.mprevLogIndex + 1
\*         IN 
\*             /\ state[i] \in { Follower, Candidate }
\*             /\ logOk
\*             \* We only truncate if terms do not match and our log index
\*             \* is >= the log of the sender. Note that we do not reset the commitIndex
\*             \* here as well, since if safety holds, then we should never be truncating a 
\*             \* portion of the log that is covered by a commitIndex.
\*             /\ m.mentries # << >>
\*             /\ Len(log[i]) >= index
\*             /\ m.mentries[1] > log[i][index]
\*             /\ state' = [state EXCEPT ![i] = Follower]
\*             /\ log' = [log EXCEPT ![i] = TruncateLog(m, i)]
\*             /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \cup {[
\*                         mtype           |-> AppendEntriesResponse,
\*                         mterm           |-> currentTerm[i],
\*                         msuccess        |-> TRUE,
\*                         mmatchIndex     |-> m.mprevLogIndex,
\*                         msource         |-> i,
\*                         mdest           |-> j]}
\*             /\ UNCHANGED <<votesGranted, nextIndex, matchIndex, commitIndex, votedFor, currentTerm, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>

AcceptAppendEntriesRequestLearnCommit(m) ==
    /\ m \in appendEntriesRequestMsgs
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm = currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == LogOk(i, m)
        IN 
            /\ state[i] \in { Follower, Candidate }
            \* We can learn a commitIndex as long as the log check passes, and if we could append these log entries.
            \* We will not, however, advance our local commitIndex to a point beyond the end of our log. And,
            \* we don't actually update our log here, only our commitIndex.

            \* PRE (can comment these conditions out to introduce bug)
            /\ logOk
            /\ Len(log[i]) = m.mprevLogIndex
            /\ CanAppend(m, i)

            /\ m.mcommitIndex > commitIndex[i] \* no need to ever decrement our commitIndex.
            /\ state' = [state EXCEPT ![i] = Follower]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.mcommitIndex, Len(log[i])})]
            \* No need to send a response message since we are not updating our logs.
            /\ UNCHANGED <<votesGranted, appendEntriesRequestMsgs, appendEntriesResponseMsgs, nextIndex, matchIndex, log, votedFor, currentTerm, requestVoteRequestMsgs, requestVoteResponseMsgs>>


\* ACTION: HandleAppendEntriesResponse
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: ({ mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
HandleAppendEntriesResponse(m) ==
    /\ m \in appendEntriesResponseMsgs
    /\ m.mtype = AppendEntriesResponse
    /\ m.mterm = currentTerm[m.mdest]
    /\ LET i     == m.mdest
           j     == m.msource
        IN
            /\ \/ /\ m.msuccess \* successful
                  /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                  /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
               \/ /\ \lnot m.msuccess \* not successful
                  /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
                  /\ UNCHANGED <<matchIndex>>
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, votesGranted, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>


\* RestartAction == TRUE /\ \E i \in Server : Restart(i)
RequestVoteAction == TRUE /\ \E i \in Server : RequestVote(i)
UpdateTermAction == TRUE /\ \E m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs : UpdateTerm(m.mterm, m.mdest)
\* UpdateTermRVReqAction == TRUE /\ \E m \in requestVoteRequestMsgs : UpdateTermRVReq(m.mterm, m.mdest)
\* UpdateTermRVResAction == TRUE /\ \E m \in requestVoteResponseMsgs : UpdateTermRVRes(m.mterm, m.mdest)
\* UpdateTermAEReqAction == TRUE /\ \E m \in appendEntriesRequestMsgs : UpdateTermAEReq(m.mterm, m.mdest)
\* UpdateTermAEResAction == TRUE /\ \E m \in appendEntriesResponseMsgs : UpdateTermAERes(m.mterm, m.mdest)
BecomeLeaderAction == TRUE /\ \E i \in Server : BecomeLeader(i)
ClientRequestAction == TRUE /\ \E i \in Server : ClientRequest(i)
AdvanceCommitIndexAction == TRUE /\ \E i \in Server : AdvanceCommitIndex(i)
AppendEntriesAction == TRUE /\ \E i,j \in Server : AppendEntries(i, j)
HandleRequestVoteRequestAction == \E m \in requestVoteRequestMsgs : HandleRequestVoteRequest(m)
HandleRequestVoteResponseAction == \E m \in requestVoteResponseMsgs : HandleRequestVoteResponse(m)
RejectAppendEntriesRequestAction == \E m \in appendEntriesRequestMsgs : RejectAppendEntriesRequest(m)
AcceptAppendEntriesRequestAppendAction == \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestAppend(m)
\* AcceptAppendEntriesRequestTruncateAction == TRUE /\ \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestTruncate(m)
AcceptAppendEntriesRequestLearnCommitAction == \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestLearnCommit(m)
HandleAppendEntriesResponseAction == \E m \in appendEntriesResponseMsgs : HandleAppendEntriesResponse(m)

Test1 == \A s \in Server : \E r \in Server :
            /\ state[s] = Leader
            /\ state[s] \in {Follower}

\* Defines how the variables may transition.
Next == 
    \/ RequestVoteAction
    \/ UpdateTermAction
    \* \/ UpdateTermRVReqAction
    \* \/ UpdateTermRVResAction
    \* \/ UpdateTermAEReqAction
    \* \/ UpdateTermAEResAction
    \/ HandleRequestVoteRequestAction
    \/ HandleRequestVoteResponseAction
    \/ BecomeLeaderAction
    \/ ClientRequestAction
    \/ AppendEntriesAction
    \/ RejectAppendEntriesRequestAction
    \/ AcceptAppendEntriesRequestAppendAction
    \/ AcceptAppendEntriesRequestLearnCommitAction
    \/ HandleAppendEntriesResponseAction 
    \/ AdvanceCommitIndexAction
    \* \/ AcceptAppendEntriesRequestTruncateAction \* (DISABLE FOR NOW FOR SMALLER PROOF)

NextUnchanged == UNCHANGED vars

L1 == ~(\E s \in Server : Len(log[s]) > 0)
\* L1 == ~(requestVoteRequestMsgs # {})

CONSTANT 
    \* @type: Int;
    MaxTerm
CONSTANT 
    \* @type: Int;
    MaxLogLen

Terms == 0..MaxTerm
LogIndices == 1..MaxLogLen
LogIndicesWithZero == 0..MaxLogLen

\* In this spec we send at most 1 log entry per AppendEntries message. 
\* We encode this in the type invariant for convenience.
MaxMEntriesLen == 1

RequestVoteRequestType == [
    mtype         : {RequestVoteRequest},
    mterm         : Terms,
    mlastLogTerm  : Terms,
    mlastLogIndex : LogIndicesWithZero,
    msource       : Server,
    mdest         : Server
]

RequestVoteResponseType == [
    mtype        : {RequestVoteResponse},
    mterm        : Terms,
    mvoteGranted : BOOLEAN,
    msource      : Server,
    mdest        : Server
]

AppendEntriesRequestType == [
    mtype      : {AppendEntriesRequest},
    mterm      : Terms,
    mprevLogIndex  : LogIndices,
    mprevLogTerm   : Terms,
    mentries       : Seq(Terms),
    mcommitIndex   : LogIndicesWithZero,
    msource        : Server,
    mdest          : Server
]

AppendEntriesResponseType == [
    mtype        : {AppendEntriesResponse},
    mterm        : Terms,
    msuccess     : BOOLEAN,
    mmatchIndex  : LogIndices,
    msource      : Server,
    mdest        : Server
]


TypeOK == 
    /\ requestVoteRequestMsgs \in SUBSET RequestVoteRequestType
    /\ requestVoteResponseMsgs \in SUBSET RequestVoteResponseType
    /\ appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType
    /\ appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType
    /\ currentTerm \in [Server -> Nat]
    /\ state       \in [Server -> {Leader, Follower, Candidate}]
    /\ votedFor    \in [Server -> ({Nil} \cup Server)]
    /\ votesGranted \in [Server -> (SUBSET Server)]
    /\ nextIndex  \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]        
    /\ log             \in [Server -> Seq(Nat)]
    /\ commitIndex     \in [Server -> Nat]
    \* Encode these basic invariants into type-correctness.
    /\ \A m \in requestVoteRequestMsgs : m.msource # m.mdest
    /\ \A m \in requestVoteResponseMsgs : m.msource # m.mdest
    /\ \A m \in appendEntriesRequestMsgs : m.msource # m.mdest
    /\ \A m \in appendEntriesResponseMsgs : m.msource # m.mdest

CurrentTermType == currentTerm \in [Server -> Nat]

\* @type: Set(Seq(Int));
\* Can be empty or contain 1 log entry.
MEntriesType == {<<>>} \cup {<<t>> : t \in Terms}

Apa_AppendEntriesRequestType == [
    mtype      : {AppendEntriesRequest},
    mterm      : Terms,
    mprevLogIndex  : LogIndicesWithZero,
    mprevLogTerm   : Terms,
    mentries       : MEntriesType,
    mcommitIndex   : LogIndicesWithZero,
    msource        : Server,
    mdest          : Server
]


Spec == Init /\ [][Next]_vars

CServerInit == {"s1", "s2", "s3"}
CServerInitSize == 3

\* CServerInit == {"s1", "s2", "s3", "s4"}
\* CServerInitSize == 4

CInit == 
    /\ Leader = "Leader"
    /\ Follower = "Follower"
    /\ Candidate = "Candidate"
    /\ Nil = "Nil"
    /\ Server = CServerInit
    /\ MaxLogLen = 3
    /\ MaxTerm = 3
    /\ RequestVoteRequest = "RequestVoteRequest"
    /\ RequestVoteResponse = "RequestVoteResponse"
    /\ AppendEntriesRequest = "AppendEntriesRequest"
    /\ AppendEntriesResponse = "AppendEntriesResponse"

\* ApaTypeOK ==
\*     \* 
\*     \* TODO: Think carefully about how to handle the bounding of these message types safely.
\*     \* 
\*     \* /\ requestVoteRequestMsgs \in SUBSET RequestVoteRequestType
\*     /\ requestVoteRequestMsgs = Gen(7)
\*     /\ \A m \in requestVoteRequestMsgs : m \in RequestVoteRequestType
\*     \* /\ requestVoteResponseMsgs \in SUBSET RequestVoteResponseType
\*     /\ requestVoteResponseMsgs = Gen(7)
\*     /\ \A m \in requestVoteResponseMsgs : m \in RequestVoteResponseType
\*     \* /\ appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType
\*     /\ appendEntriesResponseMsgs = Gen(7)
\*     /\ \A m \in appendEntriesResponseMsgs : m \in AppendEntriesResponseType
\*     \* /\ appendEntriesRequestMsgs \in SUBSET Apa_AppendEntriesRequestType
\*     /\ appendEntriesRequestMsgs = Gen(7)
\*     /\ \A m \in appendEntriesRequestMsgs : m \in Apa_AppendEntriesRequestType
\*     \* Encode these basic message invariants into type-correctness.
\*     /\ \A m \in requestVoteRequestMsgs : m.msource # m.mdest
\*     /\ \A m \in requestVoteResponseMsgs : m.msource # m.mdest
\*     /\ \A m \in appendEntriesRequestMsgs : m.msource # m.mdest
\*     /\ \A m \in appendEntriesResponseMsgs : m.msource # m.mdest
\*     /\ currentTerm \in [Server -> Terms]
\*     /\ state       \in [Server -> {Leader, Follower, Candidate}]
\*     /\ votedFor    \in [Server -> ({Nil} \cup Server)]
\*     /\ votesGranted \in [Server -> (SUBSET Server)]
\*     /\ nextIndex  \in [Server -> [Server -> LogIndicesWithZero]]
\*     /\ matchIndex \in [Server -> [Server -> LogIndicesWithZero]]    
\*     \* Constrain 'log' as a bounded sequence type.
\*     \* Note that this parameter size will, I believe, always need to be at least
\*     \* as large as the cardinality of 'Server'.
\*     /\ log = Gen(CServerInitSize)
\*     /\ \A s \in Server : \A i \in DOMAIN log[s] : log[s][i] \in Terms
\*     /\ \A s \in Server : Len(log[s]) <= MaxLogLen
\*     /\ DOMAIN log = Server
\*     /\ commitIndex     \in [Server -> LogIndicesWithZero]


----

\* INVARIANTS -------------------------

MinCommitIndex(s1, s2) ==
    IF commitIndex[s1] < commitIndex[s2]
        THEN commitIndex[s1]
        ELSE commitIndex[s2]

\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value
\* LeaderHasAllAckedValues ==
\*     \* for every acknowledged value
\*     \A v \in Value :
\*         IF acked[v] = TRUE
\*         THEN
\*             \* there does not exist a server that
\*             ~\E i \in Server :
\*                 \* is a leader
\*                 /\ state[i] = Leader
\*                 \* and which is the newest leader (aka not stale)
\*                 /\ ~\E l \in Server : 
\*                     /\ l # i
\*                     /\ currentTerm[l] > currentTerm[i]
\*                 \* and that is missing the value
\*                 /\ ~\E index \in DOMAIN log[i] :
\*                     log[i][index].value = v
\*         ELSE TRUE

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Server : state[i] = Leader /\ commitIndex[i] > 0
    THEN \E i \in Server :
           /\ state[i] = Leader
           /\ commitIndex[i] > 0
           /\ \E quorum \in SUBSET Server :
               /\ Cardinality(quorum) = (Cardinality(Server) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

\* Model checking stuff.

StateConstraint == 
    /\ \A s \in Server : currentTerm[s] <= MaxTerm
    /\ \A s \in Server : Len(log[s]) <= MaxLogLen

\**************
\* Helper lemmas.
\**************

\* START_PROOF

\* Is log entry e = <<index, term>> in the log of node 'i'.
\* InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

H_VotedForNodeInTermImpliesNodeSafeAtTerm == 
    \A s,t \in Server : (votedFor[s] = t) => currentTerm[t] >= currentTerm[s]

H_CandidateInTermVotedForItself == 
    \A s \in Server : (state[s] \in {Candidate,Leader}) => votedFor[s] = s

H_QuorumsSafeAtTerms ==
    \A s \in Server : (state[s] = Leader) => 
        (\E Q \in Quorum : 
         \A t \in Q : 
            /\ currentTerm[t] >= currentTerm[s]
            /\ (currentTerm[t] = currentTerm[s]) => votedFor[t] = s)

\* If two nodes are in the same term, then their votes granted
\* sets cannot have intersecting voters.
H_CandidateVotesGrantedInTermAreUnique ==
    \A s,t \in Server :
        (/\ s # t
         /\ state[s] = Candidate
         /\ state[t] = Candidate
         /\ currentTerm[s] = currentTerm[t]) =>
            (votesGranted[s] \cap votesGranted[t]) = {}

H_LeaderHasVotesGrantedQuorum == 
    \A s \in Server : (state[s] = Leader) => votesGranted[s] \in Quorum

\* If a node has garnered votes in a term as candidate, there must
\* be no other leader in that term in existence.
H_CandidateWithVotesGrantedInTermImplyNoOtherLeader ==
    \A s,t \in Server :
        (/\ s # t
         /\ state[s] = Candidate
         /\ votesGranted[s] \in Quorum
         /\ currentTerm[s] = currentTerm[t]) =>
            state[t] # Leader

\* Does there exist a quorum of RequestVote responses in term T
\* that support voting for server 'dest'.
ExistsRequestVoteResponseQuorum(T, dest) == 
    \E msgs \in SUBSET requestVoteResponseMsgs : 
        /\ \A m \in msgs : m.mtype = RequestVoteResponse
            /\ m.mterm = T
            /\ m.mdest = dest
            /\ m.mvoteGranted
        \* Responses form a quorum.
        /\ ({m.msource : m \in msgs} \cup {dest}) \in Quorum

\* If a successful quorum of request vote repsonses was sent in term T, then 
\* there can be no logs that exist in term T.
\* TODO: Fix this to get a correct statement here.
H_SuccessfulRequestVoteQuorumInTermImpliesNoLogsInTerm ==
    \A t \in Terms :  \* TODO: Replace 'Nat' with 'Terms'?
    \E dest \in Server : 
        (/\ ExistsRequestVoteResponseQuorum(t, dest)
         /\ (~\E l \in Server : state[l] = Leader /\ currentTerm[l] = t)) => 
            \A s \in Server : \A ind \in DOMAIN log[s] : log[s][ind] # t

H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm ==
    \A s,t \in Server :
        (state[s] = Candidate /\ votesGranted[s] \in Quorum) =>
            ~(\E i \in DOMAIN log[t] : log[t][i] = currentTerm[s])

\* H_RequestVoteInTermImpliesNoLogsInTerm == 
\*     \A s \in Server :
\*         (/\ state[s] = Candidate
\*          /\ \E m \in requestVoteMsgs : m.mtype = RequestVoteRequest /\ m.mterm = currentTerm[s]) =>
\*             \A n \in Server : \A ind \in DOMAIN log[n] : log[n][ind] # currentTerm[s]    

H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm == 
    \A s \in Server :
        (/\ state[s] = Candidate
         /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
            /\ \A n \in Server : \A ind \in DOMAIN log[n] : log[n][ind] # currentTerm[s]

H_RequestVoteRequestFromNodeInTermImpliesVotedForSelf == 
    \A m \in requestVoteRequestMsgs :
        (currentTerm[m.msource] = m.mterm) =>
            votedFor[m.msource] = m.msource

H_RequestVoteRequestFromNodeImpliesSafeAtTerm == 
    \A m \in requestVoteRequestMsgs :
        (m.mtype = RequestVoteRequest) => 
            currentTerm[m.msource] >= m.mterm

\* If a node sent a successful request vote response to node S in term T, then
\* node S must be in term >= T.
H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm == 
    \A m \in requestVoteResponseMsgs :
        (/\ m.mtype = RequestVoteResponse
         /\ m.mvoteGranted) =>
            currentTerm[m.mdest] >= m.mterm

H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm == 
    \A s \in Server :
        (/\ state[s] = Candidate
         /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
            /\ \A n \in Server : ~(state[n] = Leader /\ currentTerm[n] = currentTerm[s])

H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm == 
    \A s \in Server :
        (/\ state[s] = Candidate
         /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
            ~(\E m \in appendEntriesRequestMsgs :   
                /\ m.mtype = AppendEntriesRequest
                /\ m.mentries # <<>>
                /\ m.mentries[1] = currentTerm[s])

H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm ==
    \A s \in Server :
        (state[s] = Candidate /\ votesGranted[s] \in Quorum) =>
        ~(\E m \in appendEntriesRequestMsgs :   
            /\ m.mtype = AppendEntriesRequest
            /\ m.mentries # <<>>
            /\ m.mentries[1] = currentTerm[s])


\* If request vote response message has been sent in term T,
\* then the sender must be at least in term T.
H_RequestVoteResponseTermsMatchSource ==
    \A m \in requestVoteResponseMsgs :
        m.mtype = RequestVoteResponse => 
            /\ currentTerm[m.msource] >= m.mterm
            /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest


\* If a candidate C has garnered a set of granted votes in term T, 
\* then all of those voters must be at term T or newer, and if they
\* are in term T, then they must have voted for C.
H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm ==
    \A s \in Server : 
        (state[s] = Candidate) =>
            \A v \in votesGranted[s] : 
                /\ currentTerm[v] >= currentTerm[s]
                /\ currentTerm[v] = currentTerm[s] => votedFor[v] = s

\* H_CandidateWithVotesGrantedInTermImplyVotedForSafeAtTerm ==
\*     \A s \in Server : 
\*         (state[s] = Candidate /\ votesGranted[s] \in Quorum) =>
\*             \A v \in votesGranted[s] : 
\*                 /\ currentTerm[v] = currentTerm[s] => votedFor[v] # Nil

\* If a server exists in voteGranted for some server in term T, and the node is still in
\* term T, then it must have voted for that node.
H_VoteInGrantedImpliesVotedFor == 
    \A s,t \in Server :
        (/\ state[s] = Candidate
         /\ t \in votesGranted[s]) => 
            /\ currentTerm[t] >= currentTerm[s]
            /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s

\* A node can't have sent a RequestVoteResponse ack to two different servers in the same term.
H_RequestVoteResponseMsgsInTermUnique ==
    \A mi,mj \in requestVoteResponseMsgs :
        (/\ mi.mterm = mj.mterm
         /\ mi.msource = mj.msource
         /\ mi.mvoteGranted
         /\ mj.mvoteGranted) => mi.mdest = mj.mdest

\* If a server has granted its vote to a server S in term T, then
\* there can't be a vote response message from that server to some other server R # S.
H_VoteGrantedImpliesVoteResponseMsgConsistent ==
    \A s,t \in Server : 
    \A m \in requestVoteResponseMsgs :
        ( /\ state[s] \in {Candidate,Leader}
          /\ t \in votesGranted[s]) =>
                ~(/\ m.mterm = currentTerm[s]
                  /\ m.msource = t
                  /\ m.mdest # s
                  /\ m.mvoteGranted)

\* If a node has granted its vote to some node in term T, then the granting
\* node must be safe at term T.
H_VoteGrantedImpliesNodeSafeAtTerm == 
    \A s \in Server : 
        state[s] \in {Candidate,Leader} => 
        (\A t \in votesGranted[s] : 
            /\ currentTerm[t] >= currentTerm[s]
            /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s
        )

H_VotesCantBeGrantedTwiceToCandidatesInSameTerm ==
    \A s,t \in Server : 
        ( /\ s # t 
          /\ state[s] \in {Leader,Candidate} 
          /\ state[t] \in {Leader,Candidate} 
          /\ currentTerm[s] = currentTerm[t]) =>
            \* Cannot be intersection between voters that gave votes to candidates in same term.
            votesGranted[s] \cap votesGranted[t] = {}

\* H_VotesCantBeGrantedTwiceToCandidatesInSameTerm == 
\*     \A s,t \in Server : 
\*         \* If s voted for t.
\*         (votedFor[s] = t)

H_OnePrimaryPerTerm == 
    \A s,t \in Server : 
        (s # t /\ state[s] = Leader /\ state[t] = Leader) => currentTerm[s] # currentTerm[t]

H_CurrentTermAtLeastAsLargeAsLogTerms == 
    \A s \in Server : 
        (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

\* A server's current term is always at least as large as the terms in its log.
H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary == 
    \A s \in Server : 
        (state[s] = Leader) => 
            (\A i \in DOMAIN log[s] : currentTerm[s] >= log[s][i])

H_LogTermsMonotonic == 
    \A s \in Server : \A i,j \in DOMAIN log[s] : (i <= j) => (log[s][i] <= log[s][j])

H_LogTermsMonotonicAppendEntries == 
    \A m \in appendEntriesRequestMsgs :
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>
         /\ m.mprevLogIndex > 0) => 
            m.mentries[1] >= m.mprevLogTerm 

\* If a log entry exists in term T and there is a primary in term T, then this
\* log entry should be present in that primary's log.
H_PrimaryHasEntriesItCreated == 
    \A i,j \in Server :
    (state[i] = Leader) => 
    \* Can't be that another node has an entry in this primary's term
    \* but the primary doesn't have it.
        ~(\E k \in DOMAIN log[j] :
            /\ log[j][k] = currentTerm[i]
            /\ ~\E ind \in DOMAIN log[i] : (ind = k /\ log[i][k] = log[j][k]) 
            )

\* If an AppendEntries request has been sent with some log entries in term T, then a current
\* leader in term T must have these log entries.
H_PrimaryHasEntriesItCreatedAppendEntries == 
    \A s \in Server :
    \A m \in appendEntriesRequestMsgs :
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>> 
         /\ m.mentries[1] = currentTerm[s]
         /\ state[s] = Leader) =>
            /\ (m.mprevLogIndex + 1) \in DOMAIN log[s]
            /\ log[s][m.mprevLogIndex + 1] = m.mentries[1]

\* Existence of an entry in term T implies a past election in T, so 
\* there must be some quorum at this term or greater.
H_LogEntryInTermImpliesSafeAtTerm == 
    \A s \in Server : 
    \A i \in DOMAIN log[s] :
        \E Q \in Quorum : 
        \E u \in Server : 
            /\ currentTerm[u] >= log[s][i]
            /\ (currentTerm[u] = log[s][i]) => (state[u] = Leader)
            /\ \A n \in Q : 
                /\ currentTerm[n] >= log[s][i]
                /\ currentTerm[n] = log[s][i] => (votedFor[n] = u)

\* If a log entry appears in an AppendEntries request in a term that matches the
\* term of some candidate, then that candidate must be "nilpotent" i.e. there must
\* have been an election in that term that disabled that candidate from becoming elected
\* in future.

\* If there is a log entry that appears in an AppendEntries request in term T, this must mean
\* that the system is safe at term T i.e., an election must have occurred in term T, so a quorum
\* are safe at that term, and 
H_LogEntryInTermImpliesSafeAtTermCandidateAppendEntries == 
    \A t \in Server : 
    \A m \in appendEntriesRequestMsgs :
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>
        \*  /\ m.mentries[1] = currentTerm[t]
         /\ currentTerm[t] <= m.mentries[1] /\ state[t] # Leader
        \*  /\ state[t] = Candidate
         ) =>
            \* There is a quorum that is safe at the term, and if they voted in that term, they 
            \* must have voted for some other leader in this term i.e., not the failed candidate.
            \E Q \in Quorum : 
            \E u \in Server :
                /\ u # t
                /\ currentTerm[u] >= m.mentries[1]
                /\ currentTerm[u] = m.mentries[1] => state[u] = Leader
                /\ \A n \in Q : 
                    /\ currentTerm[n] >= m.mentries[1]
                    /\ (currentTerm[n] = m.mentries[1]) => (votedFor[n] = u)

\* If a log entry exists in some term, and there is still some candidate C in term T,
\* then there must be some quorum that voted in term T, but not for candidate C.
H_LogEntryInTermImpliesSafeAtTermCandidate == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (state[t] = Candidate /\ currentTerm[t] <= log[s][i]) =>
            \E u \in Server :
            \E Q \in Quorum : 
            \A n \in Q : 
                /\ currentTerm[n] >= log[s][i]
                \* The quorum must have voted for some leader in this term, and it is not this failed candidate.
                /\ (currentTerm[n] = log[s][i]) => ((u # t) /\ (votedFor[n] = u))

\* If an AppendEntries request was sent in term T, then there must have been a successful 
\* election in term T.
H_AppendEntriesRequestInTermImpliesSafeAtTerms == 
    \A m \in appendEntriesRequestMsgs : 
        (m.mtype = AppendEntriesRequest)  =>
            \E u \in Server :
            \E Q \in Quorum :
                /\ u = m.msource \* sender of the AppendEntries must have been leader of that term.
                /\ currentTerm[u] >= m.mterm
                /\ (currentTerm[u] = m.mterm) => state[u] = Leader
                /\ \A t \in Q : 
                    /\ currentTerm[t] >= m.mterm
                    /\ currentTerm[t] = m.mterm => (votedFor[t] = m.msource)

H_AppendEntriesResponseInTermImpliesSafeAtTerms == 
    \A m \in appendEntriesResponseMsgs : 
        ((m.mtype = AppendEntriesResponse /\ m.msuccess))  =>
            \E u \in Server :
            \E Q \in Quorum : 
                /\ u = m.mdest
                /\ currentTerm[u] >= m.mterm
                /\ (currentTerm[u] = m.mterm) => state[u] = Leader
                /\ \A t \in Q : 
                    /\ currentTerm[t] >= m.mterm
                    /\ currentTerm[t] = m.mterm => (votedFor[t] = m.mdest)

H_LogEntryInTermImpliesSafeAtTermAppendEntries ==
    \A m \in appendEntriesRequestMsgs : 
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>) =>
            \E Q \in Quorum : 
            \E u \in Server : 
                /\ currentTerm[u] >= m.mentries[1]
                /\ (currentTerm[u] = m.mentries[1]) => state[u] = Leader
                /\ \A n \in Q : 
                    /\ currentTerm[n] >= m.mentries[1]
                    /\ currentTerm[n] = m.mentries[1] => (votedFor[n] = u)


\* <<index, term>> pairs uniquely identify log prefixes.
H_LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* Log matching must hold between any two current AppendEntries requests.
H_LogMatchingBetweenAppendEntriesMsgs ==
    \A mi,mj \in appendEntriesRequestMsgs : 
        (/\ mi.mtype = AppendEntriesRequest
         /\ mj.mtype = AppendEntriesRequest  
         /\ mi.mprevLogIndex > 0
         /\ mj.mprevLogIndex > 0
         /\ mi.mprevLogIndex = mj.mprevLogIndex
         /\ mi.mentries # <<>>
         /\ mj.mentries # <<>>
         /\ mi.mentries[1] = mj.mentries[1]) =>
            mi.mprevLogTerm = mj.mprevLogTerm

\* If an AppendEntries request has been sent with log entries in term T, then these entries
\* must have been created by primary in term T, and so this entry must match the log of a leader
\* in term T.
H_LogMatchingInAppendEntriesMsgsLeaders == 
    \A m \in appendEntriesRequestMsgs : 
    \A s \in Server : 
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>
         /\ state[s] = Leader
         /\ m.mentries[1] = currentTerm[s]) => 
            /\ \E ind \in DOMAIN log[s] : (ind = m.mprevLogIndex + 1) /\ (log[s][ind] = m.mentries[1])
            /\ (m.mprevLogIndex > 0) => 
                    (\E prevInd \in DOMAIN log[s] : 
                        /\ prevInd = m.mprevLogIndex 
                        /\ log[s][prevInd] = m.mprevLogTerm)

H_LogMatchingAppendEntries ==
    \* If a server contains the log entry being sent in this AppendEntries, 
    \* then the server's previous entry must match the AppendEntries previous entry.
    \A m \in appendEntriesRequestMsgs : 
    \A s \in Server : 
        (\E ind \in DOMAIN log[s] : 
            /\ m.mtype = AppendEntriesRequest
            /\ m.mentries # <<>>
            /\ ind = m.mprevLogIndex + 1 
            /\ log[s][ind] = m.mentries[1]
            /\ m.mprevLogIndex \in DOMAIN log[s]) =>
                log[s][m.mprevLogIndex] = m.mprevLogTerm

\* Has a candidate server garnered all votes to win election in its term.
CandidateWithVoteQuorumGranted(s) == 
    /\ state[s] = Candidate
    /\ votesGranted[s] \in Quorum

H_DivergentEntriesInAppendEntriesMsgsForRequestVoteQuorum ==
    \A m \in appendEntriesRequestMsgs : 
    \A s \in Server : 
        (/\ m.mtype = AppendEntriesRequest
         /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)
         /\ m.mprevLogIndex + 1 > Len(log[s])) => 
            (m.mentries # <<>> => m.mentries[1] # currentTerm[s]) 

H_DivergentEntriesInAppendEntriesMsgs == 
    \* An AppendEntries cannot contain log entries in term T at newer indices than
    \* a leader or pending candidate's log in term T.
    \A m \in appendEntriesRequestMsgs : 
    \A s \in Server : 
        (/\ m.mtype = AppendEntriesRequest
         /\ (state[s] = Leader \/ CandidateWithVoteQuorumGranted(s))
         /\ m.mprevLogIndex + 1 > Len(log[s])) => 
            (m.mentries # <<>> => m.mentries[1] # currentTerm[s]) 


\* TODO: Consider how to state this.
\* Leader logs contain all entries committed in previous terms.
\* H_LeaderCompleteness == 
\*     \A s \in Server : (state[s] = Leader) => 
\*         \A c \in immediatelyCommitted : (c[2] < currentTerm[s] => InLog(<<c[1],c[2]>>, s))


H_RequestVotesNeverSentToSelf == 
    /\ \A m \in (requestVoteResponseMsgs) : m.msource # m.mdest
    /\ \A m \in (requestVoteRequestMsgs) : m.msource # m.mdest

H_AppendEntriesNeverSentToSelf == 
    /\ \A m \in (appendEntriesRequestMsgs) : m.msource # m.mdest
    /\ \A m \in (appendEntriesResponseMsgs) : m.msource # m.mdest

H_AppendEntriesCommitIndexCannotBeLargerThanTheSender == 
    \A m \in appendEntriesRequestMsgs :
        m.mtype = AppendEntriesRequest => 
        m.mcommitIndex <= commitIndex[m.msource] 

\* Match index records for a leader must always be <= its own log length.
H_LeaderMatchIndexBound == 
    \A s \in Server : (state[s] = Leader) => 
        \A t \in Server : matchIndex[s][t] <= Len(log[s])

H_AppendEntriesRequestImpliesSenderSafeAtTerm == 
    \A m \in appendEntriesRequestMsgs :
        (m.mtype = AppendEntriesRequest) =>
            currentTerm[m.msource] >= m.mterm

ExistsNodeQuorumThatVotedAtTermFor(T, s) == 
    \E Q \in Quorum :
    \A t \in Q :
        /\ votedFor[t] = s
        /\ currentTerm[t] = T

H_NodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm == 
    \A s \in Server :
        (/\ state[s] = Candidate
         /\ ExistsNodeQuorumThatVotedAtTermFor(currentTerm[s], s)) =>
            ~(\E m \in appendEntriesRequestMsgs : 
                /\ m.mtype = AppendEntriesRequest
                /\ m.mterm = currentTerm[s])

H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm == 
    \A s \in Server :
        (/\ state[s] = Candidate
         /\ ExistsRequestVoteResponseQuorum(currentTerm[s], s)) =>
            /\ ~(\E m \in (appendEntriesRequestMsgs) : m.mterm = currentTerm[s])
            /\ ~(\E m \in (appendEntriesResponseMsgs) : m.msuccess /\ m.mterm = currentTerm[s])

\* If a server candidate has won votes in term T, there can't be
\* any AppendEntries messages already sent in that term.
H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm == 
      \A s \in Server :
        (/\ state[s] = Candidate
         /\ votesGranted[s] \in Quorum) =>
            /\ ~\E m \in (appendEntriesRequestMsgs) : 
                    m.mtype = AppendEntriesRequest /\ m.mterm = currentTerm[s]
            /\ ~\E m \in (appendEntriesResponseMsgs) : 
                    m.mtype = AppendEntriesResponse /\ m.msuccess /\ m.mterm = currentTerm[s]


H_AppendEntriesRequestLogTermsNoGreaterThanSenderTerm == 
    \A m \in appendEntriesRequestMsgs : 
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>) =>
            m.mentries[1] <= m.mterm

\* The logs in any AppendEntries message sent in term T must be present
\* in the logs of a leader in term T.
H_AppendEntriesRequestLogEntriesMustBeInLeaderLog == 
    \A m \in appendEntriesRequestMsgs : 
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>
         /\ state[m.msource] = Leader
         /\ currentTerm[m.msource] = m.mterm) =>
            /\ Len(log[m.msource]) >= m.mprevLogIndex + 1
            /\ log[m.msource][m.mprevLogIndex + 1] = m.mentries[1]
            /\ m.mprevLogIndex > 0 => log[m.msource][m.mprevLogIndex] = m.mprevLogTerm


\* If a AppendEntries response has been sent in term T recording a match up to
\* index I, then the sender node should have the same entry as the leader.
H_LeaderMatchIndexValidAppendEntries == 
    \A m \in appendEntriesResponseMsgs : 
        (/\ m.mtype = AppendEntriesResponse
         /\ m.msuccess
         /\ m.mmatchIndex > 0
         /\ state[m.mdest] = Leader
         /\ m.mterm = currentTerm[m.mdest]) =>
            /\ Len(log[m.msource]) >= m.mmatchIndex
            /\ Len(log[m.mdest]) >= m.mmatchIndex
            /\ log[m.msource][m.mmatchIndex] = log[m.mdest][m.mmatchIndex]

\* If matchIndex on a leader has quorum agreement on an index, then this entry must
\* be present on a quorum of servers.
H_LeaderMatchIndexValid == 
    \A s \in Server :
    \A ind \in DOMAIN log[s] :
    \E Q \in Quorum : 
    \A t \in Q :
        (/\ state[s] = Leader 
         /\ Agree(s, ind) \in Quorum ) => 
            /\ ind \in DOMAIN log[t]
            /\ log[t][ind] = log[s][ind]

\* If a log entry is covered by a commit index, there cannot be a conflicting
\* log entry at that index in an AppendEntries message.
H_NoLogDivergenceAppendEntries == 
    \A s \in Server :
    \A m \in appendEntriesRequestMsgs :
        (/\ m.mtype = AppendEntriesRequest
         /\ m.mentries # <<>>
         /\ m.mprevLogIndex = commitIndex[s] - 1
         /\ commitIndex[s] <= Len(log[s])) =>
            log[s][commitIndex[s]] >= m.mentries[1]

H_LogsLaterThanCommittedMustHaveCommitted ==
    \A s,t \in Server : 
        \* Exists an entry in log[s] with a term greater than the term in which another entry was committed.
        (/\ commitIndex[t] \in DOMAIN log[t]
         /\ \E i \in DOMAIN log[s] : (log[s][i] > log[t][commitIndex[t]])) =>
                /\ Len(log[s]) >= commitIndex[t]
                /\ log[s][commitIndex[t]] = log[t][commitIndex[t]] \* entry exists in the server's log.

\* If a log entry is covered by a commit index, then a leader
\* in a newer term must have that entry.
H_LeaderHasEntriesCoveredByCommitIndexes == 
    \A s,t \in Server :
        (/\ state[s] = Leader
         /\ commitIndex[t] \in DOMAIN log[t]
         /\ currentTerm[s] > log[t][commitIndex[t]]
         /\ commitIndex[t] \in DOMAIN log[s]) =>
            log[s][commitIndex[t]] = log[t][commitIndex[t]]



H_CommitIndexCoveredOnQuorum == 
    \A s \in Server :
        (commitIndex[s] > 0) => 
            \E Q \in Quorum :
            \A t \in Q :
                /\ Len(log[s]) >= commitIndex[s] 
                /\ Len(log[t]) >= commitIndex[s] 
                /\ log[t][commitIndex[s]] = log[s][commitIndex[s]]

\* If a commit index covers a log entry in some term,
\* then no primary in an earlier term can be enabled to commit any entries
\* in its own log.
H_CommitIndexAtEntryInTermDisabledEarlierCommits == 
    \A s,t \in Server :
        (/\ s # t 
         /\ commitIndex[s] > 0
         /\ state[t] = Leader
         /\ currentTerm[t] < log[s][commitIndex[s]]) =>
                \A ind \in DOMAIN log[t] : Agree(t, ind) \notin Quorum 


\* If an AppendEntries has been sent with a commitIndex that covers some 
\* log entry in the message, there must be some node that has that entry 
\* and equal or newer commitIndex.
H_CommitIndexInAppendEntriesImpliesCommittedEntryExists == 
    \A m \in appendEntriesRequestMsgs : 
        ( /\ m.mtype = AppendEntriesRequest 
          /\ m.mcommitIndex > 0
          /\ m.mentries # <<>> 
          /\ m.mprevLogIndex > 0) =>
            (\E n \in Server :
             \E ind \in DOMAIN log[n] :
                (/\ ind = m.mprevLogIndex
                 /\ log[n][ind] = m.mprevLogTerm
                 /\ commitIndex[n] >= m.mcommitIndex))

\* Commit index is no greater than the log length on any node.
H_CommitIndexBoundValid == 
    \A s \in Server : commitIndex[s] <= Len(log[s])


\* INV: NoLogDivergence
\* If a log index is covered by a commitIndex on two different servers, then
\* the entry at that index must be the same on both servers.
H_NoLogDivergence ==
    \A s1, s2 \in Server :
        (s1 # s2) =>
            \A index \in ((DOMAIN log[s1]) \cap (DOMAIN log[s2])) : 
                \* If an index is covered by a commitIndex in both logs, then the 
                \* entry must be the same between the two servers.
                (index < commitIndex[s1] /\ index < commitIndex[s2]) =>
                    log[s1][index] = log[s2][index]

\* 
\* Some sample inductive proof obligations
\*  

OnePrimaryPerTermTypeOK == 
    \* /\ ApaTypeOK
    /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
    /\ H_OnePrimaryPerTerm

PrimaryHasEntriesItCreatedTypeOK == 
    \* /\ ApaTypeOK
    /\ H_OnePrimaryPerTerm
    /\ H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
    /\ H_PrimaryHasEntriesItCreatedAppendEntries
    /\ H_PrimaryHasEntriesItCreated


H_Inv14_R0_0_I1_0 == \A VARI \in Server : (Len(log[VARI]) >= commitIndex[VARI])
H_Inv780_R0_0_I2_1 == \A VARI \in Server : \A VARM \in appendEntriesRequestMsgs : ~(CanAppend(VARM, VARI)) \/ ((LogOk(VARI, VARM) /\ log = log))
H_Inv528_R1_0_I2_0 == \A VARI \in Server : \A VARM \in appendEntriesRequestMsgs : ~((commitIndex[VARI] > 0)) \/ ~(~(LogOk(VARI, VARM) /\ log = log))

H_Inv454_R0_0_I2_1 == \A VARI \in Server : \A VARM \in appendEntriesRequestMsgs : ~((commitIndex[VARI] > 0)) \/ ((LogOk(VARI, VARM) /\ log = log))
H_Inv210_R0_1_I3_2 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
    \A VARLOGINDI \in LogIndices : 
        ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARJ] = Leader)) \/ (~(VARLOGINDI \in DOMAIN log[VARI] /\ Agree(VARI, VARLOGINDI) \in Quorum)))
------------------------------------------------------------------------------------------------------------------------

\* 
\* Other scratchpad stuff.
\* 

\* CONSTANT 
\*     \* @type: Str;
\*     n1,
\*     \* @type: Str;
\*     n2,
\*     \* @type: Str;
\*     n3


\* \* INV: Used in debugging
\* TestInv ==
\*     /\ ~\E s,t \in Server : 
\*           /\ s # t 
\*           /\ commitIndex[s] > 0 
\*           /\ currentTerm[s] = 2
\*           /\ currentTerm[t] = 1
\*           /\ state[s] = Leader
\*           /\ Len(log[t]) > 0
\*           /\ log[s][1] = 2
\*           /\ log[t][1] = 1
\*           /\ \E m \in appendEntriesRequestMsgs : m.mterm = 2 /\ m.mcommitIndex > 0 /\ currentTerm[m.mdest] = 1

\* \* State that should be a violation of "no log divergence" i.e.
\* \* node would have an entry in older term committed same index
\* \* as conflicting entry in newer term.
\* TestInv2 ==
\*     ~\E s,t \in Server : 
\*         /\ s # t 
\*         /\ commitIndex[s] > 0 
\*         /\ currentTerm[s] = 2
\*         /\ currentTerm[t] = 2
\*         /\ state[s] = Leader
\*         /\ Len(log[t]) > 0
\*         /\ log[s][1] = 2
\*         /\ log[t][1] = 1
\*         /\ commitIndex[t] > 0

\* InitTestInv == 
\*     /\ requestVoteResponseMsgs = {}
\*     /\ appendEntriesRequestMsgs = { [ mtype |-> AppendEntriesRequest,
\*         mterm |-> 2,
\*         mdest |-> n2,
\*         msource |-> n1,
\*         mprevLogIndex |-> 0,
\*         mprevLogTerm |-> 0,
\*         mentries |-> <<2>>,
\*         mcommitIndex |-> 0 ],
\*         [ mtype |-> AppendEntriesRequest,
\*             mterm |-> 2,
\*             mdest |-> n3,
\*             msource |-> n1,
\*             mprevLogIndex |-> 0,
\*             mprevLogTerm |-> 0,
\*             mentries |-> <<2>>,
\*             mcommitIndex |-> 1 ] }
\*     /\ nextIndex = ( n1 :> (n1 :> 1 @@ n2 :> 2 @@ n3 :> 1) @@
\*         n2 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@
\*         n3 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) )
\*     /\ currentTerm = (n1 :> 2 @@ n2 :> 2 @@ n3 :> 1)
\*     /\ votedFor = (n1 :> n1 @@ n2 :> n1 @@ n3 :> n3)
\*     /\ matchIndex = ( n1 :> (n1 :> 0 @@ n2 :> 1 @@ n3 :> 0) @@
\*         n2 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@
\*         n3 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) )
\*     /\ commitIndex = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 0)
\*     /\ state = (n1 :> Leader @@ n2 :> Follower @@ n3 :> Leader)
\*     /\ requestVoteRequestMsgs = { [ mtype |-> RequestVoteRequest,
\*         mterm |-> 1,
\*         mdest |-> n1,
\*         mlastLogTerm |-> 0,
\*         mlastLogIndex |-> 0,
\*         msource |-> n3 ],
\*         [ mtype |-> RequestVoteRequest,
\*             mterm |-> 1,
\*             mdest |-> n2,
\*             mlastLogTerm |-> 0,
\*             mlastLogIndex |-> 0,
\*             msource |-> n1 ],
\*         [ mtype |-> RequestVoteRequest,
\*             mterm |-> 1,
\*             mdest |-> n2,
\*             mlastLogTerm |-> 0,
\*             mlastLogIndex |-> 0,
\*             msource |-> n3 ],
\*         [ mtype |-> RequestVoteRequest,
\*             mterm |-> 1,
\*             mdest |-> n3,
\*             mlastLogTerm |-> 0,
\*             mlastLogIndex |-> 0,
\*             msource |-> n1 ],
\*         [ mtype |-> RequestVoteRequest,
\*             mterm |-> 2,
\*             mdest |-> n2,
\*             mlastLogTerm |-> 0,
\*             mlastLogIndex |-> 0,
\*             msource |-> n1 ],
\*         [ mtype |-> RequestVoteRequest,
\*             mterm |-> 2,
\*             mdest |-> n3,
\*             mlastLogTerm |-> 0,
\*             mlastLogIndex |-> 0,
\*             msource |-> n1 ] }
\*     /\ log = (n1 :> <<2>> @@ n2 :> <<2>> @@ n3 :> <<1>>)
\*     /\ votesGranted = (n1 :> {n1, n2} @@ n2 :> {} @@ n3 :> {n2, n3})


    \* /\ ~\E msgs \in SUBSET appendEntriesMsgs : msgs # {}
    \* /\ ~(\E msgs \in (SUBSET appendEntriesMsgs) : 
    \*         /\ PrintT(SUBSET appendEntriesMsgs)
    \*         /\ msgs # {} 
    \*         /\ (\A m \in msgs : m.mtype = RequestVoteResponse))
    \* /\ PrintT({s \in Server : ExistsRequestVoteResponseQuorum(1, s)})
    \* \A n \in Server : 
    \* \A t \in Terms : 
    \*     ~ExistsRequestVoteResponseQuorum(t, n)


    \* ~\E m \in requestVoteMsgs : (m.mtype = RequestVoteResponse /\ m.mvoteGranted)
    \* ~\E s \in Server : Cardinality(votesGranted[s]) > 1
    \* /\ ~\E s,t \in Server : s # t /\ log[s] # <<>> /\ log[t] # <<>>
    \* [][~AcceptAppendEntriesRequestTruncateAction]_vars
    \* ~\E s \in Server : state[s] = Leader



\* The set of servers that agree up through index.
AgreeCopy(i, index) == {i} \cup {k \in Server : matchIndex[i][k] >= index }

AgreeIndexes(i) == {index \in DOMAIN log[i] : Agree(i, index) \in Quorum}

\* ACTION: AdvanceCommitIndex ---------------------------------
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndexCopy(i) ==
    /\ state[i] = Leader
    /\ LET \* The maximum indexes for which a quorum agrees
           agreeIndexes == AgreeIndexes(i)
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)] = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, requestVoteRequestMsgs, requestVoteResponseMsgs>>

H_NoLogDivergenceCopy ==
    \A s1, s2 \in Server :
        (s1 # s2) =>
            \A index \in ((DOMAIN log[s1]) \cap (DOMAIN log[s2])) : 
                \* If an index is covered by a commitIndex in both logs, then the 
                \* entry must be the same between the two servers.
                (index < commitIndex[s1] /\ index < commitIndex[s2]) =>
                    log[s1][index] = log[s2][index]






H_Inv598_R0_0_I2 == \A VARI \in Server : ((state[VARI] = Leader)) \/ ((H_LogMatching /\ log = log))


H_Inv23387_R3_1_I3 == \A VARI \in Server : \A VARJ \in Server : \A VARLOGINDI \in LogIndices : (VARLOGINDI \in DOMAIN log[VARI] /\ VARLOGINDI \in DOMAIN log[VARJ] /\ log[VARI][VARLOGINDI] = log[VARJ][VARLOGINDI]) \/ (~(VARLOGINDI \in DOMAIN log[VARI] /\ Agree(VARI, VARLOGINDI) \in Quorum /\ matchIndex = matchIndex)) \/ (~((state[VARJ] = Leader)))
Inv9969_R2_0_I3 == \A VARI \in Server : \A VARJ \in Server : (IsPrefix(log[VARJ], log[VARI])) \/ (~((state[VARI] = Leader))) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]))


H_Inv1276_R0_1_I2 == \A VARI \in Server : \A VARJ \in Server : (IsPrefix(log[VARI], log[VARJ])) \/ ((Len(log[VARI]) > matchIndex[VARI][VARJ]))


Inv2209_R1_0_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARM \in appendEntriesRequestMsgs : (IsPrefix(log[VARI], log[VARJ])) \/ ((LogOk(VARI, VARM) /\ log = log))
Inv3504_R1_1_I3 == \A VARI \in Server : \A VARJ \in Server : \A VARLOGINDI \in LogIndices : ((currentTerm[VARI] = currentTerm[VARJ])) \/ ((IsPrefix(log[VARJ], log[VARI])) \/ (~(VARLOGINDI \in DOMAIN log[VARI] /\ Agree(VARI, VARLOGINDI) \in Quorum /\ matchIndex = matchIndex)))


H_Inv16024_R4_2_I3 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
    \A VARLOGINDI \in LogIndices : 
        (VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = currentTerm[VARI]) \/ (~((currentTerm[VARJ] > currentTerm[VARI])) \/ (~(VARLOGINDI \in DOMAIN log[VARI])))


H_Inv20_R0_0_I1 == (H_CandidateWithVotesGrantedInTermImplyNoOtherLeader /\ state = state /\ votesGranted = votesGranted /\ currentTerm = currentTerm)
H_Inv21_R1_0_I1 == (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm)
H_Inv1680_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : (VARI \in votesGranted[VARI]) \/ (~(VARJ \in votesGranted[VARI]))
H_Inv2516_R1_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))

H_Inv29138_R5_0_I3 == 
    \A VARI \in Server : \A VARJ \in Server : 
    \A VARREQVRES \in requestVoteResponseMsgs : 
        ~((currentTerm[VARI] > currentTerm[VARJ])) \/ (~(VARREQVRES.msource = VARJ) \/ (~(VARREQVRES.mterm = currentTerm[VARI])))


===============================================================================