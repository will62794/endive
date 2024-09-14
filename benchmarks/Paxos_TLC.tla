-------------------------------- MODULE Paxos_TLC -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC, Randomization, FiniteSetsExt, Paxos

kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}


TypeOKRandom == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs1a \in SUBSET Message1a
          /\ msgs1b \in RandomSetOfSubsets(10, 4, Message1b)
          /\ msgs2a \in SUBSET Message2a
          /\ msgs2b \in kOrSmallerSubset(4, Message2b)
          /\ chosen \in SUBSET Value

============================================================================