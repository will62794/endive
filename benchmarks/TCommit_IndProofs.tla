------------------------------- MODULE TCommit_IndProofs ------------------------------
EXTENDS TCommit

\* endive.py stats
\* -----------------
\* date: 2022-08-06T22:24:59.962811
\* is_inductive: True
\* inv_size: 1
\* invcheck_duration_secs: 0
\* ctielimcheck_duration_secs: 0
\* ctigen_duration_secs: 1.2457199096679688
\* total_duration_secs: 1.2991712093353271
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
\* seed: 10
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* java_version_info: openjdk version "15.0.3" 2021-04-20 OpenJDK Runtime Environment Zulu15.32+15-CA (build 15.0.3+3) OpenJDK 64-Bit Server VM Zulu15.32+15-CA (build 15.0.3+3, mixed mode)
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts

\* The inductive invariant candidate.
IndAuto ==
  /\ TCTypeOK
  /\ TCConsistent

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TCTypeOK
    BY DEF TCTypeOK,Init,Next,IndAuto,TCConsistent
  <1>2. TCConsistent
    BY DEF TCTypeOK,Init,Next,IndAuto,TCConsistent
  <1>3. QED
    BY <1>1, <1>2 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TCTypeOK'
    BY DEF TCTypeOK,Init,Next,IndAuto,TCConsistent,Prepare,Decide
  <1>2. TCConsistent'
    <2> SUFFICES ASSUME NEW rm \in RM,
                        Prepare(rm) \/ Decide(rm)
                 PROVE  TCConsistent'
      BY DEF Next
    <2>1. CASE Prepare(rm)
      BY <2>1 DEF TCTypeOK,Init,Next,IndAuto,TCConsistent,Prepare,Decide
    <2>2. CASE Decide(rm)
      BY <2>2 DEF TCTypeOK,Init,Next,IndAuto,TCConsistent,Prepare,Decide,notCommitted,canCommit
    <2>3. QED
      BY <2>1, <2>2
    
  <1>3. QED
    BY <1>1, <1>2 DEF IndAuto
 

=============================================================================
