---- MODULE lockserver_IndProofs ----
EXTENDS lockserver

\* endive.py stats
\* -----------------
\* date: 2022-08-01T20:36:20.113024
\* is_inductive: True
\* inv_size: 2
\* invcheck_duration_secs: 0.8351531028747559
\* ctielimcheck_duration_secs: 1.1566529273986816
\* ctigen_duration_secs: 3.469104766845703
\* total_duration_secs: 5.47419285774231
\* total_num_ctis_eliminated: 12
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 2
\* total_num_invs_checked: 12
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
Inv10_1_0_def == \A VARS \in Server : \A VARC \in Client : ~(VARS \in clientlocks[VARC]) \/ (~(semaphore[VARS]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv10_1_0_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv10_1_0_def
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto,
                      Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. CASE \E c \in Client, s \in Server : Connect(c, s)
    BY <1>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv10_1_0_def,Connect,Disconnect
  <1>2. CASE \E c \in Client, s \in Server : Disconnect(c, s)
    BY <1>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv10_1_0_def,Connect,Disconnect
  <1>3. QED
    BY <1>1, <1>2 DEF Next
 
====
