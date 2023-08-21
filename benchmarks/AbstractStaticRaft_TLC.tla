---- MODULE AbstractStaticRaft_TLC ----
\* 
\* Separate spec for 'TypeOKRandom' and other TLC specific definitions
\* to avoid clashes with  Apalache type checking.
\* 
EXTENDS AbstractStaticRaft, Randomization, FiniteSetsExt

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

\* Parameters for random sampling if using it.
kNumSubsets == 10
nAvgSubsetSize == 3

\* Set of all subsets of a set of size <= k.
kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

\* Potentially use cardinality of log type to better estimate sampling parameters.
logDomain == Server
logRange == BoundedSeq(InitTerm..MaxTerm, MaxLogLen)
logCardinality == Cardinality(logRange) ^ Cardinality(logDomain)

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(5, [Server -> Terms])
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in RandomSubset(160, [logDomain -> logRange])
    /\ committed \in kOrSmallerSubset(1, (LogIndices \X Terms \X Terms))

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
    Cardinality(committed) +
    SumFnRange(currentTerm) +
    \* Sum of term values in all log entries.
    SumFnRange([s \in Server |-> SumFnRange(log[s])]) +
    \* Treat states with more nodes in Secondary as lower "cost"/"energy" states.
    SumFnRange([s \in Server |-> IF state[s] = Secondary THEN 0 ELSE 1])

=============================================================================