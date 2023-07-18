

## Monolithic Inductive Safety Proof

Given safety property `TCConsistent`, we want to prove that `TCConsistent` is an invariant of the `TwoPhase` protocol specification. To do this we need to find a sufficient inductive invariant. In the standard "monolithic" inductive proof approach, we can start by checking whether `TCConsistent` is inductive on its own, by checking

$$ Init \Rightarrow TCConsistent $$

$$ TCConsistent \wedge Next \Rightarrow TCConsistent'$$

If this holds, then we're done. Otherwise, we expect to get a *counterexample to induction* (CTI), a pair of states $(s,s')$ that violates the consecution formula. From this CTI, we can then try to come up with a strengthening lemma invariant $L_1$ that is sufficient to rule out this CTI. Then, we conjoin this lemma to our original property and continue the process i.e. checking

$$ (L_1 \wedge TCConsistent) \wedge Next \Rightarrow (L_1' \wedge TCConsistent')$$

until the overall property (with all conjoined lemmas) is inductive i.e. ending up with a final inductive invariant like

$$L_k \wedge ... \wedge L_1 \wedge TCConsistent$$


```
$ python3 endive.py --spec benchmarks/TwoPhase --seed 20 --ninvs 15000 --niters 3 --nrounds 50 --num_simulate_traces 50000 --simulate_depth 1 --tlc_workers 6 --proof_tree_mode --opt_quant_minimize
```

## Compositional Inductive Safety Proof

We argue that the "monolithic" nature of the above process is undesirable in certain ways. Particularly for very large inductive proofs, the monolithic approach provides no logical structure to the lemma invariants that are discovered along the way, and how they logically fit into the structure of an overall proof. Similarly for the generation of CTIs. There may be many "reasons" why a current inductive invariant candidate is not actually inductive, and generation of induction counterexamples arbitrarily makes it difficult for a human verifier to understand or guide the proof process based on this. As an alternative, we propose a compositional proof methodology that we refer to as *inductive proof decomposition*. In essence, this is a kind of automated assume guarantee reasoning applied at the level of a single inductive safety proof. 

Instead of proceeding in a monolithic/linear manner as in the above approach, we make decomposition a core part of the proof methodology, which we argue allows for better integration of a human into the process, and modularity in the addressing of proof obligations and counterexample generation. We base this procedure on a simple reasoning principle, that is similar to but subtly different from the inductive proof rule used in the "monolithic" approach. 

For a given goal property $S$ (which will initially be equal to the safety property we are trying to prove), we first search for a set of lemma invariants such that $S$ is inductive with respect to these lemmas. Formally, we look for a supporting invariant set $\mathcal{L} = L_1 \wedge ... \wedge L_k$ such that

$$ \mathcal{L} \wedge S \wedge Next \Rightarrow S'$$

That is, $S$ is fully inductive under the assumption of the predicates in $\mathcal{L}$. In theory we could view $\mathcal{L}$ as just a single invariant but would typically be a conjunction of smaller lemma invariants $L_1 \wedge ... \wedge L_k$. In essence, we are looking for a set of supporting lemma invariants that rule out *all* CTIs for $S$, whereas in the monolithic approach we may be content to rule out *some* CTIs for $S$ before continuing the process.

Now, after discovery of the lemmas in $\mathcal{L}$, we simply apply this decomposition procedure recursively on each non-inductive lemma in $\mathcal{L}$. So, for example, for each $L_i$, we search for supporting lemma invariants

$$\mathcal{L}_i = L_{i.1} \wedge ... \wedge L_{i.k}$$

such that

$$ \mathcal{L}_i \wedge L_i \wedge Next \Rightarrow L_i'$$


<!-- <img src="TwoPhase_ind-proof-tree.pdf"> -->