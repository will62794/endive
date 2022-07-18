---- MODULE Simple_IndProofs ----
EXTENDS Simple

\* endive.py stats
\* -----------------
\* date: 2022-08-01T20:38:51.963579
\* is_inductive: True
\* inv_size: 2
\* invcheck_duration_secs: 0.9801361560821533
\* ctielimcheck_duration_secs: 1.4184200763702393
\* ctigen_duration_secs: 4.748556852340698
\* total_duration_secs: 7.15749192237854
\* total_num_ctis_eliminated: 15
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 18
\* total_num_invs_checked: 180
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 12
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv31_1_0_def == \A VARS \in ProcSet : (pc[VARS] = "a") \/ (~(x[VARS] = 0))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ PCorrect
  /\ Inv31_1_0_def

ASSUME NType == (N \in Nat) /\ (N > 0)
ASSUME ProcType == ProcSet \in SUBSET Nat

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv31_1_0_def, ProcSet
  <1>2. PCorrect
    BY NType DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv31_1_0_def, ProcSet
  <1>3. Inv31_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv31_1_0_def
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY NType DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv31_1_0_def, proc, a, b, ProcSet
  <1>2. PCorrect'
    BY NType DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv31_1_0_def, proc, a, b, ProcSet
  <1>3. Inv31_1_0_def'
    BY NType DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv31_1_0_def, proc, a, b, ProcSet
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto
 
====
