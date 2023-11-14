---- MODULE SimpleConsensus_TLC ----
EXTENDS SimpleConsensus,Randomization

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

TypeOKRandom ==
    /\ vote_request_msg \in RandomSubset(40, SUBSET (Node \X Node)) 
    /\ voted \in RandomSubset(7, [Node -> BOOLEAN])
    /\ vote_msg \in RandomSubset(40, SUBSET(Node \X Node)) 
    /\ votes \in RandomSubset(10, [Node -> SUBSET Node]) 
    /\ leader \in RandomSubset(4, [Node -> BOOLEAN])
    /\ decided \in RandomSubset(10, [Node -> SUBSET Value]) 

Symmetry == Permutations(Node) \cup Permutations(Value)

====