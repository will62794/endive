---- MODULE two_phase_commit_IndProofs ----
EXTENDS two_phase_commit

\* endive.py stats
\* -----------------
\* date: 2022-08-03T00:16:17.205265
\* is_inductive: True
\* inv_size: 11
\* invcheck_duration_secs: 10.691004276275635
\* ctielimcheck_duration_secs: 27.401139974594116
\* ctigen_duration_secs: 26.458534717559814
\* total_duration_secs: 64.70636224746704
\* total_num_ctis_eliminated: 10408
\* total_num_cti_elimination_rounds: 3
\* total_num_invs_generated: 3027
\* total_num_invs_checked: 10901
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 11
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv703_1_0_def == (go_abort = {}) \/ ((go_commit = {}))
Inv1049_1_1_def == \A VARJ \in Node : ~(VARJ \in vote_no) \/ (~(VARJ \in vote_yes))
Inv648_1_2_def == (decide_abort = {}) \/ ((go_commit = {}))
Inv699_1_3_def == (decide_commit = {}) \/ (~(go_commit = {}))
Inv346_1_4_def == \A VARJ \in Node : (VARJ \in alive) \/ ((abort_flag))
Inv313_1_5_def == \A VARI \in Node : (VARI \in vote_yes) \/ ((go_commit = {}))
Inv588_1_0_def == (abort_flag) \/ ((go_abort = {}))
Inv591_1_1_def == (abort_flag) \/ ((vote_no = {}))
Inv2455_2_2_def == \A VARI \in Node : (VARI \in go_abort) \/ ((decide_abort = {})) \/ (~(vote_no = {}))
Inv192_1_0_def == \A VARI \in Node : (VARI \in go_abort) \/ ((go_abort = {}))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv703_1_0_def
  /\ Inv1049_1_1_def
  /\ Inv648_1_2_def
  /\ Inv699_1_3_def
  /\ Inv346_1_4_def
  /\ Inv313_1_5_def
  /\ Inv588_1_0_def
  /\ Inv591_1_1_def
  /\ Inv2455_2_2_def
  /\ Inv192_1_0_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>2. Safety'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>3. Inv703_1_0_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>4. Inv1049_1_1_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>5. Inv648_1_2_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>6. Inv699_1_3_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>7. Inv346_1_4_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>8. Inv313_1_5_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>9. Inv588_1_0_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>10. Inv591_1_1_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>11. Inv2455_2_2_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>12. Inv192_1_0_def'
    BY DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,IndAuto,Safety,Inv703_1_0_def,Inv1049_1_1_def,Inv648_1_2_def,Inv699_1_3_def,Inv346_1_4_def,Inv313_1_5_def,Inv588_1_0_def,Inv591_1_1_def,Inv2455_2_2_def,Inv192_1_0_def
  <1>13. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
 
====

