---- MODULE lockserv_automaton_IndProofs ----
EXTENDS lockserv_automaton

\* endive.py stats
\* -----------------
\* date: 2022-08-01T20:40:44.948594
\* is_inductive: True
\* inv_size: 9
\* invcheck_duration_secs: 3.6202454566955566
\* ctielimcheck_duration_secs: 8.511093854904175
\* ctigen_duration_secs: 6.537862062454224
\* total_duration_secs: 18.69947385787964
\* total_num_ctis_eliminated: 3624
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 262
\* total_num_invs_checked: 1140
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
Inv60_1_1_def == \A VARI \in Node : (held) \/ (~(holds_lock[VARI]))
Inv147_1_2_def == \A VARI \in Node : \A VARJ \in Node : ~(grant_msg[VARI]) \/ (~(holds_lock[VARJ]))
Inv169_1_3_def == \A VARI \in Node : \A VARJ \in Node : ~(holds_lock[VARI]) \/ (~(unlock_msg[VARJ]))
Inv58_1_4_def == \A VARI \in Node : (held) \/ (~(grant_msg[VARI]))
Inv64_1_5_def == \A VARI \in Node : (held) \/ (~(unlock_msg[VARI]))
Inv96_2_6_def == \A VARI \in Node : \A VARJ \in Node : (VARI=VARJ) \/ (~(grant_msg[VARJ])) \/ (~(grant_msg[VARI]))
Inv134_2_7_def == \A VARI \in Node : \A VARJ \in Node : (VARI=VARJ) \/ (~(unlock_msg[VARI]) \/ (~(unlock_msg[VARJ])))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Mutex
  /\ Inv151_1_0_def
  /\ Inv60_1_1_def
  /\ Inv147_1_2_def
  /\ Inv169_1_3_def
  /\ Inv58_1_4_def
  /\ Inv64_1_5_def
  /\ Inv96_2_6_def
  /\ Inv134_2_7_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>2. Mutex
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>3. Inv151_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>4. Inv60_1_1_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>5. Inv147_1_2_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>6. Inv169_1_3_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>7. Inv58_1_4_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>8. Inv64_1_5_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>9. Inv96_2_6_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>10. Inv134_2_7_def
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def
  <1>11. QED
    BY <1>1, <1>10, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>2. Mutex'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>3. Inv151_1_0_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>4. Inv60_1_1_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>5. Inv147_1_2_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>6. Inv169_1_3_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>7. Inv58_1_4_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>8. Inv64_1_5_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>9. Inv96_2_6_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>10. Inv134_2_7_def'
    BY DEF TypeOK,Init,Next,IndAuto,Mutex,Inv151_1_0_def,Inv60_1_1_def,Inv147_1_2_def,Inv169_1_3_def,Inv58_1_4_def,Inv64_1_5_def,Inv96_2_6_def,Inv134_2_7_def,
           Lock,Unlock,RecvLock,RecvGrant,RecvUnlock
  <1>11. QED
    BY <1>1, <1>10, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
 

====
