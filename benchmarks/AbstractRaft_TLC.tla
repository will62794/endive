---- MODULE AbstractRaft_TLC ----
\* 
\* Separate spec for 'TypeOKRandom' and other TLC specific definitions
\* to avoid clashes with  Apalache type checking.
\* 
EXTENDS AbstractRaft, Randomization, FiniteSetsExt

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

\* Parameters for random sampling if using it.
kNumSubsets == 10
nAvgSubsetSize == 3

\* Set of all subsets of a set of size <= k.
kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

TypeOK == 
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> BoundedSeq(Terms, MaxLogLen)]
    /\ immediatelyCommitted \in SUBSET (LogIndices \X Terms)

TypeOKSmallCommitted == 
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> BoundedSeq(Terms, MaxLogLen)]
    /\ immediatelyCommitted \in kOrSmallerSubset(1, (LogIndices \X Terms))

TypeOKSmallCommitted2 == 
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> BoundedSeq(Terms, MaxLogLen)]
    /\ immediatelyCommitted \in kOrSmallerSubset(2, (LogIndices \X Terms))

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(5, [Server -> Terms])
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in RandomSubset(80, [Server -> BoundedSeq(Terms, MaxLogLen)])
    /\ immediatelyCommitted \in kOrSmallerSubset(2, (LogIndices \X Terms))

TypeOKRandomEmptyCommitted == 
    /\ currentTerm \in RandomSubset(5, [Server -> Terms])
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in RandomSubset(80, [Server -> BoundedSeq(Terms, MaxLogLen)])
    /\ immediatelyCommitted = {}

\* Old, randomized version.
\* /\ committed \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, (LogIndices \X Terms \X Terms))

\* 
\* CTI cost definitions.
\* 

\* Sum the elements in the range of a function.
RECURSIVE SumFnRange(_)
SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
  LET x == CHOOSE x \in DOMAIN f : TRUE
    IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s))

RECURSIVE SetSum(_)
SetSum(set) == IF set = {} THEN 0 ELSE
  LET x == CHOOSE x \in set: TRUE
    IN x + SetSum(set \ {x})

\* Predicate determining a "cost" function for CTI, typically to measure complexity/size of a 
\* given CTI i.e. if we want to look for "minimal" CTIs.
CTICost == 
    \* Sum of all log lengths.
    SumFnRange([s \in Server |-> Len(log[s])]) + 
    Cardinality(immediatelyCommitted) +
    SumFnRange(currentTerm) +
    \* Sum of term values in all log entries.
    SumFnRange([s \in Server |-> SumFnRange(log[s])]) +
    \* Treat states with more nodes in Secondary as lower "cost"/"energy" states.
    SumFnRange([s \in Server |-> IF state[s] = Secondary THEN 0 ELSE 1])



\* 
\* Liveness. (TODO.)
\* 

\* Simple high level liveness property of a system with bounded logs
\* that says that all indices eventually become committed.
\* EventuallyAllIndicesCommit == <> (\A s \in Server : Len(log[s]) = MaxLogLen)
EventuallyAllIndicesCommit == []((\E s,t \in Server : log[s] # log[t]) => <>(\A s,t \in Server : log[s] = log[t]))
\* EventuallyAllIndicesCommit == <> ({c[1] : c \in committed} = LogIndices)
\* EventuallyAllIndicesCommit == <> (Cardinality(committed) > 4)
\* EventuallyAllIndicesCommit == <> (\E s \in Server : currentTerm[s] = -2)

HInv1 == 
    \E s,t \in Server : 
        /\ s # t
        /\ log[s] = <<1>> 
        /\ state[t] = Primary
        /\ currentTerm[t] = 2
        /\ log[t] = <<2>>
        /\ \A q \in Server : q \notin {s,t} => log[q] = <<>>

HInv1Check == ~HInv1

\* TODO: What are proper fairness assumptions here?
Fairness ==
    \* /\ \A s \in Server : WF_vars(ClientRequest(s))
    /\ \A s, t \in Server : WF_vars(GetEntries(s, t))
    /\ \A s, t \in Server : WF_vars(RollbackEntries(s, t))
    \* /\ \A s \in Server : \A Q \in Quorums(Server) : WF_vars(BecomeLeader(s, Q))
    /\ \A s \in Server :  \A Q \in Quorums(Server) : WF_vars(CommitEntry(s, Q))
    /\ \A s,t \in Server : WF_vars(UpdateTerms(s, t))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
