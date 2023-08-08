---- MODULE AbstractStaticRaft_TypeOKRandom ----
\* 
\* Separate spec for definition of 'TypeOKRandom' to avoid clashes with
\* Apalache type checking.
\* 
EXTENDS AbstractStaticRaft, Randomization

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)
NumRandSubsets == 13

kNumSubsets == 10
nAvgSubsetSize == 3

TypeOKRandom == 
    /\ currentTerm \in RandomSubset(5, [Server -> Terms])
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> BoundedSeq(InitTerm..MaxTerm, MaxLogLen)]
    /\ committed \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, (LogIndices \X Terms \X Terms))

=============================================================================
