--------------------------------- MODULE AsyncRaft_TLC ---------------------------------
EXTENDS AsyncRaft, FiniteSetsExt, Randomization



\* Set of all subsets of a set of size <= k.
kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

\* 
\* Work around size limitations of TLC subset computations.
\* 

\* RequestVoteResponseTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteResponseTypeOp({t})) : t \in Terms }
\* RequestVoteRequestTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteRequestTypeOp({t})) : t \in Terms }

RequestVoteRequestTypeSampled == RandomSetOfSubsets(2, 2, RequestVoteRequestType) 
RequestVoteResponseTypeSampled == RandomSetOfSubsets(2, 2, RequestVoteResponseType)  
AppendEntriesRequestTypeSampled == RandomSetOfSubsets(3, 3, AppendEntriesRequestType)
AppendEntriesResponseTypeSampled == RandomSetOfSubsets(3, 3, AppendEntriesResponseType)  

TypeOKRandom == 
    /\ requestVoteRequestMsgs \in RequestVoteRequestTypeSampled
    /\ requestVoteResponseMsgs \in RequestVoteResponseTypeSampled
    /\ appendEntriesRequestMsgs \in AppendEntriesRequestTypeSampled
    /\ appendEntriesResponseMsgs \in AppendEntriesResponseTypeSampled
    /\ currentTerm \in [Server -> Terms]
    /\ state       \in [Server -> {Leader, Follower, Candidate}]
    /\ votedFor    \in [Server -> ({Nil} \cup Server)]
    /\ votesGranted \in [Server -> (SUBSET Server)]
    /\ nextIndex  \in [Server -> [Server -> LogIndices]]
    /\ matchIndex \in [Server -> [Server -> LogIndicesWithZero]]        
    /\ log             \in [Server -> BoundedSeq(Terms, MaxLogLen)]
    /\ commitIndex     \in [Server -> LogIndicesWithZero]
    \* Encode these basic invariants into type-correctness.
    /\ \A m \in requestVoteRequestMsgs : m.msource # m.mdest
    /\ \A m \in requestVoteResponseMsgs : m.msource # m.mdest
    /\ \A m \in appendEntriesRequestMsgs : m.msource # m.mdest
    /\ \A m \in appendEntriesResponseMsgs : m.msource # m.mdest



\* Sum the elements in the range of a function.
RECURSIVE SumFnRange(_)
SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
  LET x == CHOOSE x \in DOMAIN f : TRUE
    IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

CTICost == 
    SumFnRange([s \in Server |-> Cardinality(votesGranted[s])]) +
    SumFnRange([s \in Server |-> Len(log[s])]) +
    SumFnRange(currentTerm) + 
    SumFnRange(commitIndex) + 
    Cardinality(requestVoteRequestMsgs \cup requestVoteResponseMsgs) + 
    Cardinality(appendEntriesRequestMsgs \cup appendEntriesResponseMsgs) + 
    SumFnRange([s \in Server |-> IF state[s] \in {Follower,Candidate} THEN 0 ELSE 1])


===============================================================================