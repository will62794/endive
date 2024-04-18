--------------------------- MODULE LamportMutex_IndProofs ----------------------------
(***************************************************************************)
(* TLA+ specification of Lamport's distributed mutual-exclusion algorithm  *)
(* that appeared as an example in                                          *)
(* L. Lamport:  Time, Clocks and the Ordering of Events in a Distributed   *)
(* System. CACM 21(7):558-565, 1978.                                       *)
(***************************************************************************)
EXTENDS LamportMutex, FiniteSets, SequenceTheorems, TLAPS


\* DISCOVERY 2024.


\* Proof Graph Stats
\* ==================
\* seed: 3
\* num proof graph nodes: 17
\* num proof obligations: 102
Safety == Mutex
Inv186_R0_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
Inv275_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
Inv364_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv165_R0_0_I1 == \A VARI \in Proc : (\A VOTHER \in Proc \ {VARI} : beats(VARI,VOTHER) /\ req = req) \/ (~(VARI \in crit))
Inv1001_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack"))
Inv39_R2_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
Inv1320_R3_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv757_R4_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(VARJ \in crit))
Inv35_R4_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ crit = crit) \/ (~(network[VARI][VARJ] # <<>>))
Inv166_R4_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))
Inv574_R5_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
Inv832_R5_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "rel") \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] > Head(network[VARJ][VARI]).clock))
Inv46_R8_3_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).clock > clock[VARI])
Inv938_R12_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].type = "rel") \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] > Head(network[VARJ][VARI]).clock))
Inv23_R13_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].clock > clock[VARI])
Inv603_R14_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] = 0) \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] = Head(network[VARJ][VARI]).clock))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv186_R0_0_I1
  /\ Inv275_R0_0_I1
  /\ Inv1001_R2_0_I1
  /\ Inv35_R4_0_I1
  /\ Inv574_R5_1_I1
  /\ Inv757_R4_0_I1
  /\ Inv39_R2_1_I1
  /\ Inv364_R0_0_I1
  /\ Inv1320_R3_0_I1
  /\ Inv166_R4_1_I1
  /\ Inv165_R0_0_I1
  /\ Inv832_R5_1_I1
  /\ Inv938_R12_1_I1
  /\ Inv603_R14_1_I1
  /\ Inv46_R8_3_I1
  /\ Inv23_R13_0_I1


\* mean in-degree: 1.3529411764705883
\* median in-degree: 1
\* max in-degree: 4
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A1 == Nats \subseteq Nat
USE A1


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,RequestAction)
  <1>1. TypeOK /\ TypeOK /\ RequestAction => TypeOK'
       BY DEF TypeOK,RequestAction,Request,TypeOK
  \* (TypeOK,EnterAction)
  <1>2. TypeOK /\ TypeOK /\ EnterAction => TypeOK'
       BY DEF TypeOK,EnterAction,Enter,TypeOK,beats
  \* (TypeOK,ExitAction)
  <1>3. TypeOK /\ TypeOK /\ ExitAction => TypeOK'
       BY DEF TypeOK,ExitAction,Exit,TypeOK,beats,Broadcast
  \* (TypeOK,ReceiveRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ReceiveRequestAction => TypeOK'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,TypeOK
  \* (TypeOK,ReceiveAckAction)
  <1>5. TypeOK /\ TypeOK /\ ReceiveAckAction => TypeOK'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,TypeOK,beats
  \* (TypeOK,ReceiveReleaseAction)
  <1>6. TypeOK /\ TypeOK /\ ReceiveReleaseAction => TypeOK'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,TypeOK,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Safety /\ Next => Safety'
  \* (Safety,RequestAction)
  <1>1. TypeOK /\ Safety /\ RequestAction => Safety'
       BY DEF TypeOK,RequestAction,Request,Safety,Mutex
  \* (Safety,EnterAction)
  <1>2. TypeOK /\ Safety /\ EnterAction => Safety'
       BY DEF TypeOK,EnterAction,Enter,Safety,beats,Mutex
  \* (Safety,ExitAction)
  <1>3. TypeOK /\ Safety /\ ExitAction => Safety'
       BY DEF TypeOK,ExitAction,Exit,Safety,beats,Broadcast,Mutex
  \* (Safety,ReceiveRequestAction)
  <1>4. TypeOK /\ Safety /\ ReceiveRequestAction => Safety'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Safety,Mutex
  \* (Safety,ReceiveAckAction)
  <1>5. TypeOK /\ Safety /\ ReceiveAckAction => Safety'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Safety,beats,Mutex
  \* (Safety,ReceiveReleaseAction)
  <1>6. TypeOK /\ Safety /\ ReceiveReleaseAction => Safety'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Safety,beats,Mutex
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv186_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv186_R0_0_I1 /\ Next => Inv186_R0_0_I1'
  \* (Inv186_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv186_R0_0_I1 /\ RequestAction => Inv186_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv186_R0_0_I1
  \* (Inv186_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv186_R0_0_I1 /\ EnterAction => Inv186_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv186_R0_0_I1,beats
  \* (Inv186_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv186_R0_0_I1 /\ ExitAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv186_R0_0_I1,beats,Broadcast
  \* (Inv186_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv186_R0_0_I1 /\ ReceiveRequestAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv186_R0_0_I1
  \* (Inv186_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv186_R0_0_I1 /\ ReceiveAckAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv186_R0_0_I1,beats
  \* (Inv186_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv186_R0_0_I1 /\ ReceiveReleaseAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv186_R0_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv275_R0_0_I1
THEOREM L_3 == TypeOK /\ Inv275_R0_0_I1 /\ Next => Inv275_R0_0_I1'
  \* (Inv275_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv275_R0_0_I1 /\ RequestAction => Inv275_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv275_R0_0_I1
  \* (Inv275_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv275_R0_0_I1 /\ EnterAction => Inv275_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv275_R0_0_I1,beats
  \* (Inv275_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv275_R0_0_I1 /\ ExitAction => Inv275_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv275_R0_0_I1,beats,Broadcast
  \* (Inv275_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv275_R0_0_I1 /\ ReceiveRequestAction => Inv275_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv275_R0_0_I1
  \* (Inv275_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv275_R0_0_I1 /\ ReceiveAckAction => Inv275_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv275_R0_0_I1,beats
  \* (Inv275_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv275_R0_0_I1 /\ ReceiveReleaseAction => Inv275_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv275_R0_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1001_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv1001_R2_0_I1 /\ Next => Inv1001_R2_0_I1'
  \* (Inv1001_R2_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1001_R2_0_I1 /\ RequestAction => Inv1001_R2_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv1001_R2_0_I1
  \* (Inv1001_R2_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1001_R2_0_I1 /\ EnterAction => Inv1001_R2_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv1001_R2_0_I1,beats
  \* (Inv1001_R2_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv1001_R2_0_I1 /\ ExitAction => Inv1001_R2_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv1001_R2_0_I1,beats,Broadcast
  \* (Inv1001_R2_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1001_R2_0_I1 /\ ReceiveRequestAction => Inv1001_R2_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1001_R2_0_I1
  \* (Inv1001_R2_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1001_R2_0_I1 /\ ReceiveAckAction => Inv1001_R2_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1001_R2_0_I1,beats
  \* (Inv1001_R2_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1001_R2_0_I1 /\ ReceiveReleaseAction => Inv1001_R2_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1001_R2_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv35_R4_0_I1
THEOREM L_5 == TypeOK /\ Inv35_R4_0_I1 /\ Next => Inv35_R4_0_I1'
  \* (Inv35_R4_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv35_R4_0_I1 /\ RequestAction => Inv35_R4_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv35_R4_0_I1
  \* (Inv35_R4_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv35_R4_0_I1 /\ EnterAction => Inv35_R4_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv35_R4_0_I1,beats
  \* (Inv35_R4_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv35_R4_0_I1 /\ ExitAction => Inv35_R4_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv35_R4_0_I1,beats,Broadcast
  \* (Inv35_R4_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv35_R4_0_I1 /\ ReceiveRequestAction => Inv35_R4_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv35_R4_0_I1
  \* (Inv35_R4_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv35_R4_0_I1 /\ ReceiveAckAction => Inv35_R4_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv35_R4_0_I1,beats
  \* (Inv35_R4_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv35_R4_0_I1 /\ ReceiveReleaseAction => Inv35_R4_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv35_R4_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv574_R5_1_I1
THEOREM L_6 == TypeOK /\ Inv574_R5_1_I1 /\ Next => Inv574_R5_1_I1'
  \* (Inv574_R5_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv574_R5_1_I1 /\ RequestAction => Inv574_R5_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv574_R5_1_I1
  \* (Inv574_R5_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv574_R5_1_I1 /\ EnterAction => Inv574_R5_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv574_R5_1_I1,beats
  \* (Inv574_R5_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv574_R5_1_I1 /\ ExitAction => Inv574_R5_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv574_R5_1_I1,beats,Broadcast
  \* (Inv574_R5_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv574_R5_1_I1 /\ ReceiveRequestAction => Inv574_R5_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv574_R5_1_I1
  \* (Inv574_R5_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv574_R5_1_I1 /\ ReceiveAckAction => Inv574_R5_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv574_R5_1_I1,beats
  \* (Inv574_R5_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv574_R5_1_I1 /\ ReceiveReleaseAction => Inv574_R5_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv574_R5_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv757_R4_0_I1
THEOREM L_7 == TypeOK /\ Inv757_R4_0_I1 /\ Next => Inv757_R4_0_I1'
  \* (Inv757_R4_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv757_R4_0_I1 /\ RequestAction => Inv757_R4_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv757_R4_0_I1
  \* (Inv757_R4_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv757_R4_0_I1 /\ EnterAction => Inv757_R4_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv757_R4_0_I1,beats
  \* (Inv757_R4_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv757_R4_0_I1 /\ ExitAction => Inv757_R4_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv757_R4_0_I1,beats,Broadcast
  \* (Inv757_R4_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv757_R4_0_I1 /\ ReceiveRequestAction => Inv757_R4_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv757_R4_0_I1
  \* (Inv757_R4_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv757_R4_0_I1 /\ ReceiveAckAction => Inv757_R4_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv757_R4_0_I1,beats
  \* (Inv757_R4_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv757_R4_0_I1 /\ ReceiveReleaseAction => Inv757_R4_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv757_R4_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv39_R2_1_I1
THEOREM L_8 == TypeOK /\ Inv39_R2_1_I1 /\ Next => Inv39_R2_1_I1'
  \* (Inv39_R2_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_R2_1_I1 /\ RequestAction => Inv39_R2_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv39_R2_1_I1
  \* (Inv39_R2_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv39_R2_1_I1 /\ EnterAction => Inv39_R2_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv39_R2_1_I1,beats
  \* (Inv39_R2_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv39_R2_1_I1 /\ ExitAction => Inv39_R2_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv39_R2_1_I1,beats,Broadcast
  \* (Inv39_R2_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv39_R2_1_I1 /\ ReceiveRequestAction => Inv39_R2_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv39_R2_1_I1
  \* (Inv39_R2_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv39_R2_1_I1 /\ ReceiveAckAction => Inv39_R2_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv39_R2_1_I1,beats
  \* (Inv39_R2_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv39_R2_1_I1 /\ ReceiveReleaseAction => Inv39_R2_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv39_R2_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv364_R0_0_I1
THEOREM L_9 == TypeOK /\ Inv364_R0_0_I1 /\ Next => Inv364_R0_0_I1'
  \* (Inv364_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv364_R0_0_I1 /\ RequestAction => Inv364_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv364_R0_0_I1 /\ EnterAction => Inv364_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv364_R0_0_I1,beats
  \* (Inv364_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv364_R0_0_I1 /\ ExitAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv364_R0_0_I1,beats,Broadcast
  \* (Inv364_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv364_R0_0_I1 /\ ReceiveRequestAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv364_R0_0_I1 /\ ReceiveAckAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv364_R0_0_I1,beats
  \* (Inv364_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv364_R0_0_I1 /\ ReceiveReleaseAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv364_R0_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1320_R3_0_I1
THEOREM L_10 == TypeOK /\ Inv1320_R3_0_I1 /\ Next => Inv1320_R3_0_I1'
  \* (Inv1320_R3_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1320_R3_0_I1 /\ RequestAction => Inv1320_R3_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv1320_R3_0_I1
  \* (Inv1320_R3_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1320_R3_0_I1 /\ EnterAction => Inv1320_R3_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv1320_R3_0_I1,beats
  \* (Inv1320_R3_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv1320_R3_0_I1 /\ ExitAction => Inv1320_R3_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv1320_R3_0_I1,beats,Broadcast
  \* (Inv1320_R3_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1320_R3_0_I1 /\ ReceiveRequestAction => Inv1320_R3_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1320_R3_0_I1
  \* (Inv1320_R3_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1320_R3_0_I1 /\ ReceiveAckAction => Inv1320_R3_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1320_R3_0_I1,beats
  \* (Inv1320_R3_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1320_R3_0_I1 /\ ReceiveReleaseAction => Inv1320_R3_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1320_R3_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv166_R4_1_I1
THEOREM L_11 == TypeOK /\ Inv166_R4_1_I1 /\ Next => Inv166_R4_1_I1'
  \* (Inv166_R4_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv166_R4_1_I1 /\ RequestAction => Inv166_R4_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv166_R4_1_I1
  \* (Inv166_R4_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv166_R4_1_I1 /\ EnterAction => Inv166_R4_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv166_R4_1_I1,beats
  \* (Inv166_R4_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv166_R4_1_I1 /\ ExitAction => Inv166_R4_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv166_R4_1_I1,beats,Broadcast
  \* (Inv166_R4_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv166_R4_1_I1 /\ ReceiveRequestAction => Inv166_R4_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv166_R4_1_I1
  \* (Inv166_R4_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv166_R4_1_I1 /\ ReceiveAckAction => Inv166_R4_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv166_R4_1_I1,beats
  \* (Inv166_R4_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv166_R4_1_I1 /\ ReceiveReleaseAction => Inv166_R4_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv166_R4_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv165_R0_0_I1
THEOREM L_12 == TypeOK /\ Inv165_R0_0_I1 /\ Next => Inv165_R0_0_I1'
  \* (Inv165_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv165_R0_0_I1 /\ RequestAction => Inv165_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv165_R0_0_I1
  \* (Inv165_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv165_R0_0_I1 /\ EnterAction => Inv165_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv165_R0_0_I1,beats
  \* (Inv165_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv165_R0_0_I1 /\ ExitAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv165_R0_0_I1,beats,Broadcast
  \* (Inv165_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv165_R0_0_I1 /\ ReceiveRequestAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv165_R0_0_I1
  \* (Inv165_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv165_R0_0_I1 /\ ReceiveAckAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv165_R0_0_I1,beats
  \* (Inv165_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv165_R0_0_I1 /\ ReceiveReleaseAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv165_R0_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv832_R5_1_I1
THEOREM L_13 == TypeOK /\ Inv832_R5_1_I1 /\ Next => Inv832_R5_1_I1'
  \* (Inv832_R5_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv832_R5_1_I1 /\ RequestAction => Inv832_R5_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv832_R5_1_I1
  \* (Inv832_R5_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv832_R5_1_I1 /\ EnterAction => Inv832_R5_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv832_R5_1_I1,beats
  \* (Inv832_R5_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv832_R5_1_I1 /\ ExitAction => Inv832_R5_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv832_R5_1_I1,beats,Broadcast
  \* (Inv832_R5_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv832_R5_1_I1 /\ ReceiveRequestAction => Inv832_R5_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv832_R5_1_I1
  \* (Inv832_R5_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv832_R5_1_I1 /\ ReceiveAckAction => Inv832_R5_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv832_R5_1_I1,beats
  \* (Inv832_R5_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv832_R5_1_I1 /\ ReceiveReleaseAction => Inv832_R5_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv832_R5_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv938_R12_1_I1
THEOREM L_14 == TypeOK /\ Inv938_R12_1_I1 /\ Next => Inv938_R12_1_I1'
  \* (Inv938_R12_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv938_R12_1_I1 /\ RequestAction => Inv938_R12_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv938_R12_1_I1
  \* (Inv938_R12_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv938_R12_1_I1 /\ EnterAction => Inv938_R12_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv938_R12_1_I1,beats
  \* (Inv938_R12_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv938_R12_1_I1 /\ ExitAction => Inv938_R12_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv938_R12_1_I1,beats,Broadcast
  \* (Inv938_R12_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv938_R12_1_I1 /\ ReceiveRequestAction => Inv938_R12_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv938_R12_1_I1
  \* (Inv938_R12_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv938_R12_1_I1 /\ ReceiveAckAction => Inv938_R12_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv938_R12_1_I1,beats
  \* (Inv938_R12_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv938_R12_1_I1 /\ ReceiveReleaseAction => Inv938_R12_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv938_R12_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv603_R14_1_I1
THEOREM L_15 == TypeOK /\ Inv603_R14_1_I1 /\ Next => Inv603_R14_1_I1'
  \* (Inv603_R14_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv603_R14_1_I1 /\ RequestAction => Inv603_R14_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv603_R14_1_I1
  \* (Inv603_R14_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv603_R14_1_I1 /\ EnterAction => Inv603_R14_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv603_R14_1_I1,beats
  \* (Inv603_R14_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv603_R14_1_I1 /\ ExitAction => Inv603_R14_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv603_R14_1_I1,beats,Broadcast
  \* (Inv603_R14_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv603_R14_1_I1 /\ ReceiveRequestAction => Inv603_R14_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv603_R14_1_I1
  \* (Inv603_R14_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv603_R14_1_I1 /\ ReceiveAckAction => Inv603_R14_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv603_R14_1_I1,beats
  \* (Inv603_R14_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv603_R14_1_I1 /\ ReceiveReleaseAction => Inv603_R14_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv603_R14_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv46_R8_3_I1
THEOREM L_16 == TypeOK /\ Inv46_R8_3_I1 /\ Next => Inv46_R8_3_I1'
  \* (Inv46_R8_3_I1,RequestAction)
  <1>1. TypeOK /\ Inv46_R8_3_I1 /\ RequestAction => Inv46_R8_3_I1'
       BY DEF TypeOK,RequestAction,Request,Inv46_R8_3_I1
  \* (Inv46_R8_3_I1,EnterAction)
  <1>2. TypeOK /\ Inv46_R8_3_I1 /\ EnterAction => Inv46_R8_3_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv46_R8_3_I1,beats
  \* (Inv46_R8_3_I1,ExitAction)
  <1>3. TypeOK /\ Inv46_R8_3_I1 /\ ExitAction => Inv46_R8_3_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv46_R8_3_I1,beats,Broadcast
  \* (Inv46_R8_3_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv46_R8_3_I1 /\ ReceiveRequestAction => Inv46_R8_3_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv46_R8_3_I1
  \* (Inv46_R8_3_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv46_R8_3_I1 /\ ReceiveAckAction => Inv46_R8_3_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv46_R8_3_I1,beats
  \* (Inv46_R8_3_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv46_R8_3_I1 /\ ReceiveReleaseAction => Inv46_R8_3_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv46_R8_3_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv23_R13_0_I1
THEOREM L_17 == TypeOK /\ Inv23_R13_0_I1 /\ Next => Inv23_R13_0_I1'
  \* (Inv23_R13_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv23_R13_0_I1 /\ RequestAction => Inv23_R13_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv23_R13_0_I1
  \* (Inv23_R13_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv23_R13_0_I1 /\ EnterAction => Inv23_R13_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv23_R13_0_I1,beats
  \* (Inv23_R13_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv23_R13_0_I1 /\ ExitAction => Inv23_R13_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv23_R13_0_I1,beats,Broadcast
  \* (Inv23_R13_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv23_R13_0_I1 /\ ReceiveRequestAction => Inv23_R13_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv23_R13_0_I1
  \* (Inv23_R13_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv23_R13_0_I1 /\ ReceiveAckAction => Inv23_R13_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv23_R13_0_I1,beats
  \* (Inv23_R13_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv23_R13_0_I1 /\ ReceiveReleaseAction => Inv23_R13_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv23_R13_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17 DEF Next, IndGlobal


==============================================================================
==============================================================================