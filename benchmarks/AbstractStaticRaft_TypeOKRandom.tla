---- MODULE AbstractStaticRaft_TypeOKRandom ----
\* 
\* Separate spec for definition of 'TypeOKRandom' to avoid clashes with
\* Apalache type checking.
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

=============================================================================
