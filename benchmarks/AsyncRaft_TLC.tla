--------------------------------- MODULE AsyncRaft_TLC ---------------------------------
EXTENDS AsyncRaft, Randomization



\* Set of all subsets of a set of size <= k.
\* kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

\* 
\* Work around size limitations of TLC subset computations.
\* 

\* RequestVoteResponseTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteResponseTypeOp({t})) : t \in Terms }
\* RequestVoteRequestTypeSampled == UNION { kOrSmallerSubset(2, RequestVoteRequestTypeOp({t})) : t \in Terms }


\* Terms == 0..MaxTerm
\* LogIndices == 1..MaxLogLen
\* LogIndicesWithZero == 0..MaxLogLen

\* Symmetry == Permutations(Server)

\* \* In this spec we send at most 1 log entry per AppendEntries message. 
\* \* We encode this in the type invariant for convenience.
\* MaxMEntriesLen == 1

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

RequestVoteRequestTypeBounded == [
    mtype         : {RequestVoteRequest},
    mterm         : Terms,
    mlastLogTerm  : Terms,
    mlastLogIndex : LogIndicesWithZero,
    msource       : Server,
    mdest         : Server
]

RequestVoteResponseTypeBounded == [
    mtype        : {RequestVoteResponse},
    mterm        : Terms,
    mvoteGranted : BOOLEAN,
    msource      : Server,
    mdest        : Server
]

AppendEntriesRequestTypeBounded == [
    mtype      : {AppendEntriesRequest},
    mterm      : Terms,
    mprevLogIndex  : LogIndices,
    mprevLogTerm   : Terms,
    mentries       : BoundedSeq(Terms, MaxMEntriesLen),
    mcommitIndex   : LogIndicesWithZero,
    msource        : Server,
    mdest          : Server
]

AppendEntriesResponseTypeBounded == [
    mtype        : {AppendEntriesResponse},
    mterm        : Terms,
    msuccess     : BOOLEAN,
    mmatchIndex  : LogIndices,
    msource      : Server,
    mdest        : Server
]

RequestVoteRequestTypeSampled == RandomSetOfSubsets(3, 3, RequestVoteRequestTypeBounded) 
RequestVoteResponseTypeSampled == RandomSetOfSubsets(3, 3, RequestVoteResponseTypeBounded)  
AppendEntriesRequestTypeSampled == RandomSetOfSubsets(2, 2, AppendEntriesRequestTypeBounded) \cup RandomSetOfSubsets(3, 3, AppendEntriesRequestTypeBounded)
AppendEntriesResponseTypeSampled == RandomSetOfSubsets(1, 1, AppendEntriesResponseTypeBounded) \cup RandomSetOfSubsets(2, 2, AppendEntriesResponseTypeBounded) \cup RandomSetOfSubsets(3, 3, AppendEntriesResponseTypeBounded)  

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

Symmetry == Permutations(Server)

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