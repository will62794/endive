---- MODULE basic_consensus_TLC ----
EXTENDS basic_consensus

\* Sum the elements in the range of a function.
RECURSIVE SumFnRange(_)
SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
  LET x == CHOOSE x \in DOMAIN f : TRUE
    IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

CTICost == 
    Cardinality(vote_msg) + 
    Cardinality(vote_request_msg) + 
    SumFnRange([n \in Node |-> Cardinality(decided[n])]) +
    SumFnRange([n \in Node |-> Cardinality(votes[n])])

====