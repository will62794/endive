---- MODULE consensus_epr_TLC ----
EXTENDS consensus_epr,Randomization

\* Sum the elements in the range of a function.
\* RECURSIVE SumFnRange(_)
\* SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
\*   LET x == CHOOSE x \in DOMAIN f : TRUE
\*     IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

CTICost == 0
    \* Cardinality(vote_msg) + 
    \* Cardinality(vote_request_msg) + 
    \* SumFnRange([n \in Node |-> Cardinality(decided[n])]) +
    \* SumFnRange([n \in Node |-> Cardinality(votes[n])])
\* kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

TypeOKRandom ==
    \* /\ vote_request_msg \in kOrSmallerSubset(4, (Node \X Node)) 
    /\ vote_request_msg \in RandomSubset(40, SUBSET (Node \X Node)) 
    /\ voted \in RandomSubset(7, [Node -> BOOLEAN])
    /\ vote_msg \in RandomSubset(40, SUBSET(Node \X Node)) 
    \* /\ vote_msg \in kOrSmallerSubset(4, (Node \X Node)) 
    /\ votes \in RandomSubset(10, [Node -> SUBSET Node]) 
    /\ leader \in RandomSubset(4, [Node -> BOOLEAN])
    /\ decided \in RandomSubset(10, [Node -> SUBSET Value]) 

Symmetry == Permutations(Node) \cup Permutations(Value)

====