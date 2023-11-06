---- MODULE Zab_TLC ----
EXTENDS Zab,TLC

\* Model checking stuff.

Symmetry == Permutations(Server)

NextUnchanged == UNCHANGED vars

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

CTICost == 
    SumFnRange([s \in Server |-> Len(history[s])]) +
    SumFnRange(currentEpoch) +
    SumFnRange([s \in Server |-> Cardinality(ackeRecv[s])]) +
    SumFnRange([s \in Server |-> Cardinality(cepochRecv[s])]) +
    SumFnRange([<<s,t>> \in Server \X Server |-> Len(msgs[s][t])])

====