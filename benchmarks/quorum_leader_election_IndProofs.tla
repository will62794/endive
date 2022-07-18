---- MODULE quorum_leader_election_IndProofs ----
EXTENDS quorum_leader_election

\* endive.py stats
\* -----------------
\* date: 2022-08-01T20:37:08.237334
\* is_inductive: True
\* inv_size: 2
\* invcheck_duration_secs: 1.3358678817749023
\* ctielimcheck_duration_secs: 1.7536170482635498
\* ctigen_duration_secs: 6.9433581829071045
\* total_duration_secs: 10.044521808624268
\* total_num_ctis_eliminated: 204
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 19
\* total_num_invs_checked: 112
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: False
\* tlc_workers: 8
\* seed: 10
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv55_1_0_def == \A VARS \in Node : \A VART \in Node : \A Q \in Quorums : \E VARN \in Q : (voted[VARN] = VARS) \/ (~(isleader[VARS]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv55_1_0_def
  
ASSUME QuorumType == Quorums \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorums : Q # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME NilType == Nil \notin Node

\* TLAPS Proof skeleton.
 THEOREM Init => IndAuto 
   <1> SUFFICES ASSUME Init
                PROVE  IndAuto
     OBVIOUS
   <1>1. TypeOK
     BY QuorumType, QuorumsAreNonEmpty DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def
   <1>2. Inv
     BY QuorumType DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def
   <1>3. Inv55_1_0_def
     BY QuorumType, QuorumsAreNonEmpty DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def
   <1>4. QED
     BY <1>1, <1>2, <1>3 DEF IndAuto
  
 THEOREM IndAuto /\ Next => IndAuto'
   <1> SUFFICES ASSUME IndAuto,
                       Next
                PROVE  IndAuto'
     OBVIOUS
   <1>1. CASE \E i,j \in Node : Vote(i,j)
     <2>1. TypeOK'
       BY <1>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def,Vote,BecomeLeader
     <2>2. Inv'
       BY <1>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def,Vote,BecomeLeader
     <2>3. Inv55_1_0_def'
       BY <1>1, QuorumType, QuorumsAreNonEmpty, NodeFinite, QuorumsIntersect, NilType DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def,Vote
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF IndAuto
     
   <1>2. CASE \E i \in Node : \E Q \in Quorums : BecomeLeader(i, Q)
     <2>1. TypeOK'
       BY <1>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def,Vote,BecomeLeader
     <2>2. Inv'
       BY <1>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def,Vote,BecomeLeader
     <2>3. Inv55_1_0_def'
       BY <1>2, QuorumsIntersect, QuorumType, QuorumsAreNonEmpty, NodeFinite  DEF TypeOK,Init,Next,IndAuto,Inv,Inv55_1_0_def,Vote,BecomeLeader
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF IndAuto
     
   <1>3. QED
     BY <1>1, <1>2 DEF Next
  
====
