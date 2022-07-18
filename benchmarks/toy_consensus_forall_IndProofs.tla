---- MODULE toy_consensus_forall_IndProofs ----
EXTENDS toy_consensus_forall

\* endive.py stats
\* -----------------
\* date: 2022-08-01T20:38:14.322369
\* is_inductive: True
\* inv_size: 3
\* invcheck_duration_secs: 1.1260368824005127
\* ctielimcheck_duration_secs: 1.9848048686981201
\* ctigen_duration_secs: 11.332494974136353
\* total_duration_secs: 14.453804016113281
\* total_num_ctis_eliminated: 412
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 18
\* total_num_invs_checked: 220
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: False
\* tlc_workers: 8
\* seed: 12
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv150_1_0_def == \A s,t \in Node : \A Q \in Quorums : \A v \in Value : \E n \in Q : (voted[s]) \/ (~(vote[s] = v))
Inv65_1_1_def == \A s,t \in Node : \A Q \in Quorums : \A v \in Value : \E n \in Q : (vote[n] = v) \/ (~(v \in decided))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv150_1_0_def
  /\ Inv65_1_1_def

ASSUME QuorumType == Quorums \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorums : Q # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME NilType == Nil \notin Value

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def
  <1>2. Inv
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def
  <1>3. Inv150_1_0_def
    BY QuorumType, NodeFinite, QuorumsAreNonEmpty, NilType DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def
  <1>4. Inv65_1_1_def
    BY QuorumType, NodeFinite, QuorumsAreNonEmpty, NilType DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def
  <1>5. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, CastVote
    <2>2. CASE \E v \in Value, Q \in Quorums : Decide(v, Q)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, Decide
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  <1>2. Inv'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, CastVote
    <2>2. CASE \E v \in Value, Q \in Quorums : Decide(v, Q)
      BY <2>2, QuorumType, NodeFinite, QuorumsAreNonEmpty, NilType DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, Decide
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  <1>3. Inv150_1_0_def'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, CastVote
    <2>2. CASE \E v \in Value, Q \in Quorums : Decide(v, Q)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, Decide
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  <1>4. Inv65_1_1_def'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, CastVote
    <2>2. CASE \E v \in Value, Q \in Quorums : Decide(v, Q)
      BY <2>2, QuorumType, NodeFinite, QuorumsAreNonEmpty, NilType, QuorumsIntersect DEF TypeOK,Init,Next,IndAuto,Inv,Inv150_1_0_def,Inv65_1_1_def, Decide
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  <1>5. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF IndAuto
 
====
