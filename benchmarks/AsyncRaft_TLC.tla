--------------------------------- MODULE AsyncRaft_TLC ---------------------------------
EXTENDS AsyncRaft

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
    Cardinality(appendEntriesMsgs) + 
    SumFnRange([s \in Server |-> IF state[s] \in {Follower,Candidate} THEN 0 ELSE 1])


===============================================================================