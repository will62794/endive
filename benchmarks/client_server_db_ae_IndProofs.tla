---- MODULE client_server_db_ae_IndProofs ----
EXTENDS client_server_db_ae, FiniteSetTheorems, TLAPS

\* endive.py stats
\* -----------------
\* date: 2022-08-06T21:50:37.222098
\* is_inductive: True
\* inv_size: 8
\* invcheck_duration_secs: 4641.535584688187
\* ctielimcheck_duration_secs: 45.152153968811035
\* ctigen_duration_secs: 236.54026198387146
\* total_duration_secs: 4923.506470680237
\* total_num_ctis_eliminated: 12546
\* total_num_cti_elimination_rounds: 2
\* total_num_invs_generated: 463
\* total_num_invs_checked: 6430
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 24
\* seed: 21
\* os: posix
\* system: Linux
\* java_exe: java -Xss4M
\* processor: x86_64
\* cpu_count: 48

\* Inductive strengthening conjuncts
Inv273_1_0_def == \A VARI \in Node : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))
Inv209_1_1_def == \A VARJ \in Node : \A VARP \in Response : (<<VARJ,VARP>> \in response_sent) \/ (~(<<VARJ,VARP>> \in response_received))
Inv3082_2_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARJ \in Node : (VARI=VARJ /\ match = match) \/ (~(<<VARID,VARI>> \in t)) \/ (~(<<VARID,VARJ>> \in t))
Inv380_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : ~(<<VARID,VARP>> \in db_response_sent) \/ (~(NoneWithId(VARID)))
Inv388_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : ~(<<VARID,VARR>> \in db_request_sent) \/ (~(NoneWithId(VARID)))
Inv2868_2_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARID,VARI>> \in t) \/ (~(<<VARID,VARP>> \in db_response_sent)))
Inv873_2_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : (<<VARI,VARR>> \in request_sent) \/ (~(<<VARID,VARI>> \in t)) \/ (~(<<VARID,VARR>> \in db_request_sent))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv273_1_0_def
  /\ Inv209_1_1_def
  /\ Inv3082_2_2_def
  /\ Inv380_1_0_def
  /\ Inv388_1_1_def
  /\ Inv2868_2_2_def
  /\ Inv873_2_3_def

ASSUME Fin == IsFiniteSet(Node) /\ IsFiniteSet(Request) /\ IsFiniteSet(Response) /\ IsFiniteSet(DbRequestId)
ASSUME Nonempty == Request # {} /\ Response # {} /\ Node # {} /\ DbRequestId # {}

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>2. Safety'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>3. Inv273_1_0_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>4. Inv209_1_1_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>5. Inv3082_2_2_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>6. Inv380_1_0_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>7. Inv388_1_1_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>8. Inv2868_2_2_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>9. Inv873_2_3_def'
    <2>1. CASE \E n \in Node, r \in Request : NewRequest(n,r)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>2. CASE \E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>3. CASE \E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>4. CASE \E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>5. CASE \E n \in Node, p \in Response : ReceiveResponse(n,p)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv273_1_0_def,Inv209_1_1_def,Inv3082_2_2_def,Inv380_1_0_def,Inv388_1_1_def,Inv2868_2_2_def,Inv873_2_3_def,
      NewRequest,ServerProcessRequest,DbProcessRequest,ServerProcessDbResponse,ReceiveResponse,ResponseMatched,NoneWithId
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
  <1>10. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
    
  


====
