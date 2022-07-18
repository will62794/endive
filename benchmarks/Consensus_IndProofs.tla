----------------------------- MODULE Consensus_IndProofs ------------------------------ 
EXTENDS Consensus,FiniteSetTheorems

\* invgen.py stats
\* -----------------
\* date: 2022-07-26T23:10:26.006658
\* is_inductive: True
\* inv_size: 1
\* invcheck_duration_secs: 0
\* ctielimcheck_duration_secs: 0
\* ctigen_duration_secs: 0.9454421997070312
\* total_duration_secs: 0.9580879211425781
\* total_num_ctis_eliminated: 0
\* total_num_cti_elimination_rounds: 0
\* total_num_invs_generated: 0
\* total_num_invs_checked: 0
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 13
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv

ASSUME Fin == IsFiniteSet(Value)

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY Fin,FS_Subset DEF TypeOK,Init,Next,IndAuto,Inv
  <1>2. Inv
    BY Fin,FS_Subset,FS_EmptySet DEF TypeOK,Init,Next,IndAuto,Inv
  <1>3. QED
    BY <1>1, <1>2 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY Fin,FS_Subset,FS_EmptySet DEF TypeOK,Init,Next,IndAuto,Inv
  <1>2. Inv'
    <2>1. TypeOK'
      BY Fin,FS_Subset,FS_EmptySet,FS_Singleton DEF TypeOK,Init,Next,IndAuto,Inv
    <2>2. (Cardinality(chosen) \leq 1)'
      BY Fin,FS_Subset,FS_EmptySet,FS_Singleton DEF TypeOK,Init,Next,IndAuto,Inv
    <2>3. QED
      BY <2>1, <2>2 DEF Inv
    
  <1>3. QED
    BY <1>1, <1>2 DEF IndAuto
 
=============================================================================
