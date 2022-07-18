---- MODULE client_server_ae_IndProofs ----
EXTENDS client_server_ae, FiniteSetTheorems

\* endive.py stats
\* -----------------
\* date: 2022-08-07T13:13:29.901277
\* is_inductive: True
\* inv_size: 2
\* invcheck_duration_secs: 1.5558500289916992
\* ctielimcheck_duration_secs: 4.081765174865723
\* ctigen_duration_secs: 27.741323947906494
\* total_duration_secs: 33.48468089103699
\* total_num_ctis_eliminated: 10000
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 4
\* total_num_invs_checked: 144
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 6
\* seed: 13
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java
\* java_version_info: openjdk version "15.0.3" 2021-04-20 OpenJDK Runtime Environment Zulu15.32+15-CA (build 15.0.3+3) OpenJDK 64-Bit Server VM Zulu15.32+15-CA (build 15.0.3+3, mixed mode)
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv93_1_0_def == \A VARI \in Node : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv93_1_0_def
  
ASSUME Fin == IsFiniteSet(Node) /\ IsFiniteSet(Request) /\ IsFiniteSet(Response)
ASSUME Nonempty == Request # {} /\ Response # {}

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def
  <1>2. Safety
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def
  <1>3. Inv93_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto,
                      Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
    <2>1. TypeOK'
      BY <1>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>2. Safety'
      BY <1>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>3. Inv93_1_0_def'
      BY <1>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF IndAuto
    
  <1>2. CASE \E n \in Node, r \in Request, p \in Response : Respond(n,r,p)
    <2>1. TypeOK'
      BY <1>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>2. Safety'
      BY <1>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>3. Inv93_1_0_def'
      BY <1>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF IndAuto
    
  <1>3. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
    <2>1. TypeOK'
      BY <1>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>2. Safety'
      BY <1>3, Fin, Nonempty DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>3. Inv93_1_0_def'
      BY <1>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv93_1_0_def,ResponseMatched,NewRequest,Respond,ReceiveResponse
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF IndAuto
    
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF Next
    
    
 
====
