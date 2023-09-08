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
    SumFnRange(currentTerm)

===============================================================================