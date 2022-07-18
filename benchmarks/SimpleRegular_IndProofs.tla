---- MODULE SimpleRegular_IndProofs ----
EXTENDS SimpleRegular

\* endive.py stats
\* -----------------
\* date: 2022-08-01T20:41:29.182120
\* is_inductive: True
\* inv_size: 4
\* invcheck_duration_secs: 1.44685697555542
\* ctielimcheck_duration_secs: 2.992962121963501
\* ctigen_duration_secs: 4.984469413757324
\* total_duration_secs: 9.432929992675781
\* total_num_ctis_eliminated: 1972
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 165
\* total_num_invs_checked: 1104
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
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv417_1_0_def == \A VARS \in ProcSet : (1 \in x[VARS]) \/ ((pc[VARS] = "a1"))
Inv921_1_1_def == \A VARS \in ProcSet : ~(0 \in x[VARS]) \/ (~(pc[VARS] = "Done"))
Inv924_1_2_def == \A VARS \in ProcSet : ~(0 \in x[VARS]) \/ (~(pc[VARS] = "b"))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ PCorrect
  /\ Inv417_1_0_def
  /\ Inv921_1_1_def
  /\ Inv924_1_2_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,ProcSet
  <1>2. PCorrect
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,ProcSet
  <1>3. Inv417_1_0_def
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def
  <1>4. Inv921_1_1_def
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def
  <1>5. Inv924_1_2_def
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto
 

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,a1,a2,b,proc
  <1>2. PCorrect'
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,a1,a2,b,proc,ProcSet
  <1>3. Inv417_1_0_def'
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,a1,a2,b,proc,ProcSet
  <1>4. Inv921_1_1_def'
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,a1,a2,b,proc,ProcSet
  <1>5. Inv924_1_2_def'
    BY NAssump DEF TypeOK,Init,Next,IndAuto,PCorrect,Inv417_1_0_def,Inv921_1_1_def,Inv924_1_2_def,a1,a2,b,proc,ProcSet
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto
 
 
====
