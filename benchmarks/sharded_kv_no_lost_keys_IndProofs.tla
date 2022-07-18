---- MODULE sharded_kv_no_lost_keys_IndProofs ----
EXTENDS sharded_kv_no_lost_keys, FiniteSetTheorems

\* endive.py stats
\* -----------------
\* date: 2022-08-05T19:29:54.095415
\* is_inductive: True
\* inv_size: 2
\* invcheck_duration_secs: 1.4542489051818848
\* ctielimcheck_duration_secs: 2.2698278427124023
\* ctigen_duration_secs: 7.955007791519165
\* total_duration_secs: 11.684753894805908
\* total_num_ctis_eliminated: 404
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 179
\* total_num_invs_checked: 264
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
Inv45_1_0_def == \A KI \in Key : \E NJ \in Node : \E VALI \in Value : (<<NJ,KI,VALI>> \in transfer_msg) \/ ((KI \in owner[NJ]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv45_1_0_def
  
ASSUME Fin == IsFiniteSet(Node) /\ IsFiniteSet(Key) /\ IsFiniteSet(Value)
ASSUME NonEmpty == Node # {} /\ Value # {} /\ Key # {}

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def
  <1>2. Safety
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def
  <1>3. Inv45_1_0_def
    BY NonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto
 

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      BY <2>1, Fin,NonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def,Reshard,RecvTransferMsg,Put
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      BY <2>2, Fin,NonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def,Reshard,RecvTransferMsg,Put
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin,NonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>2. Safety'
    BY Fin,NonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def,Reshard,RecvTransferMsg,Put
  <1>3. Inv45_1_0_def'
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv45_1_0_def,Reshard,RecvTransferMsg,Put
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto
 
 
====
