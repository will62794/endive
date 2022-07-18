---- MODULE lockserv_IndProofs ----
EXTENDS lockserv

\* endive.py stats
\* -----------------
\* date: 2022-08-02T23:33:26.222821
\* is_inductive: True
\* inv_size: 9
\* invcheck_duration_secs: 6.777111530303955
\* ctielimcheck_duration_secs: 13.321575403213501
\* ctigen_duration_secs: 9.559056282043457
\* total_duration_secs: 29.70569896697998
\* total_num_ctis_eliminated: 3654
\* total_num_cti_elimination_rounds: 2
\* total_num_invs_generated: 410
\* total_num_invs_checked: 1760
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
Inv151_1_0_def == \A VARI \in Node : \A VARJ \in Node : ~(grant_msg[VARI]) \/ (~(unlock_msg[VARJ]))
Inv162_1_1_def == \A VARI \in Node : ~(holds_lock[VARI]) \/ (~(server_holds_lock))
Inv146_1_2_def == \A VARI \in Node : \A VARJ \in Node : ~(grant_msg[VARI]) \/ (~(holds_lock[VARJ]))
Inv164_1_3_def == \A VARI \in Node : \A VARJ \in Node : ~(holds_lock[VARI]) \/ (~(unlock_msg[VARJ]))
Inv149_1_4_def == \A VARI \in Node : ~(grant_msg[VARI]) \/ (~(server_holds_lock))
Inv177_1_5_def == \A VARI \in Node : ~(server_holds_lock) \/ (~(unlock_msg[VARI]))
Inv96_2_6_def == \A VARI \in Node : \A VARJ \in Node : (VARI=VARJ) \/ (~(grant_msg[VARJ])) \/ (~(grant_msg[VARI]))
Inv128_2_0_def == \A VARI \in Node : \A VARJ \in Node : (VARI=VARJ) \/ (~(unlock_msg[VARI]) \/ (~(unlock_msg[VARJ])))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Mutex
  /\ Inv151_1_0_def
  /\ Inv162_1_1_def
  /\ Inv146_1_2_def
  /\ Inv164_1_3_def
  /\ Inv149_1_4_def
  /\ Inv177_1_5_def
  /\ Inv96_2_6_def
  /\ Inv128_2_0_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>2. Mutex'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>3. Inv151_1_0_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>4. Inv162_1_1_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>5. Inv146_1_2_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>6. Inv164_1_3_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>7. Inv149_1_4_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>8. Inv177_1_5_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>9. Inv96_2_6_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>10. Inv128_2_0_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>11. QED
    BY <1>1, <1>10, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
 

====
