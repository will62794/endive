---- MODULE AbstractStaticRaft_TypeOKRandom ----
\* 
\* Separate spec for definition of 'TypeOKRandom' to avoid clashes with
\* Apalache type checking.
\* 
EXTENDS AbstractStaticRaft, Randomization, FiniteSetsExt

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

\* Parameters for random sampling if using it.
NumRandSubsets == 13
kNumSubsets == 10
nAvgSubsetSize == 3

\* Set of all subsets of a set of size <= k.
kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(5, [Server -> Terms])
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> BoundedSeq(InitTerm..MaxTerm, MaxLogLen)]
    /\ committed \in kOrSmallerSubset(2, (LogIndices \X Terms \X Terms))

\* Old, randomized version.
\* /\ committed \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, (LogIndices \X Terms \X Terms))

=============================================================================
