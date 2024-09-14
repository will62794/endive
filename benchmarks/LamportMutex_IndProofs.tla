--------------------------- MODULE LamportMutex_IndProofs ----------------------------
(***************************************************************************)
(* TLA+ specification of Lamport's distributed mutual-exclusion algorithm  *)
(* that appeared as an example in                                          *)
(* L. Lamport:  Time, Clocks and the Ordering of Events in a Distributed   *)
(* System. CACM 21(7):558-565, 1978.                                       *)
(***************************************************************************)
EXTENDS LamportMutex, FiniteSets, SequenceTheorems, TLAPS


\* Proof Graph Stats
\* ==================
\* seed: 4
\* num proof graph nodes: 32
\* num proof obligations: 192
Safety == Mutex
Inv13148_14cd_R0_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(beats(VARI,VARJ) /\ req = req)) \/ (~(ack[VARI] = Proc))
Inv3213_dc35_R1_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (VARI \in crit) \/ ((req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ])))
Inv63_dd88_R1_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv4953_fa98_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(network[VARI][VARI] # <<>>))
Inv2144_a275_R1_1_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
Inv691_75d7_R1_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "rel") > 0) \/ (~(VARI \in crit))
Inv357_3058_R1_3_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "req") > 0) \/ (~(VARI \in crit))
Inv57_6f6e_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
Inv1125_1f8c_R2_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(Count(network[VARI][VARJ], "ack") > 0))
Inv1056_5a8d_R2_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "rel") > 0) \/ (~(VARJ \in ack[VARI]))
Inv604_e925_R3_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "ack") > 0) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv10_af7e_R3_1_I0 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].clock > req[VARI][VARI])
Inv15_c48d_R4_0_I0 == \A VARI \in Proc : ~(network[VARI][VARI] # <<>>)
Inv39_8f4b_R5_0_I1 == \A VARI \in Proc : (ack[VARI] = {}) \/ ((req[VARI][VARI] > 0))
Inv637_d0fa_R7_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "req") > 0) \/ (~(ack[VARI] = Proc))
Inv1703_12c5_R7_1_I1 == \A VARI \in Proc : (req[VARI][VARI] > 0) \/ (~(VARI \in crit))
Inv792_b5c0_R9_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "ack") > 0) \/ (~(Count(network[VARJ][VARI], "rel") > 0))
Inv885_f510_R11_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "ack") > 0) \/ (~(VARJ \in crit))
Inv526_6f2c_R14_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARJ][VARI], "ack") > 0) \/ (~(ack[VARI] = {}))
Inv168_a109_R15_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARJ \in ack[VARI]))
Inv172_01bd_R15_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "ack") > 0) \/ (~(Count(network[VARJ][VARI], "req") > 0))
Inv264_199a_R17_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "rel") > 0) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "req"))
Inv1072_3196_R18_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARJ][VARI], "ack") > 0) \/ (~(ack[VARI] = Proc))
Inv375_3bd9_R19_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "req") > 0) \/ (~(ack[VARI] = {}))
Inv73_44a3_R20_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(Count(network[VARJ][VARI], "ack") > 0))
Inv2_3687_R21_0_I0 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "req") <= 1)
Inv1052_ce44_R21_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARI] > 0) \/ (~(Count(network[VARJ][VARI], "ack") > 0))
Inv363_5241_R23_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(Count(network[VARI][VARJ], "ack") > 0) \/ (~(VARI \in ack[VARJ]))
Inv139_ec0b_R23_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "ack") <= 1) \/ ((VARI \in ack[VARJ]) \/ (~(network[VARI][VARJ] # <<>>)))
Inv997_9dba_R26_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARI] > 0) \/ (~(Count(network[VARI][VARJ], "req") > 0))
Inv8_6351_R28_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "ack") <= 1) \/ ((VARI \in ack[VARJ]))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv13148_14cd_R0_0_I2
  /\ Inv3213_dc35_R1_0_I2
  /\ Inv57_6f6e_R2_0_I1
  /\ Inv1125_1f8c_R2_1_I1
  /\ Inv15_c48d_R4_0_I0
  /\ Inv792_b5c0_R9_1_I1
  /\ Inv885_f510_R11_0_I1
  /\ Inv1072_3196_R18_0_I1
  /\ Inv73_44a3_R20_0_I1
  /\ Inv2_3687_R21_0_I0
  /\ Inv997_9dba_R26_0_I1
  /\ Inv357_3058_R1_3_I1
  /\ Inv637_d0fa_R7_0_I1
  /\ Inv168_a109_R15_0_I1
  /\ Inv172_01bd_R15_0_I1
  /\ Inv1052_ce44_R21_1_I1
  /\ Inv1703_12c5_R7_1_I1
  /\ Inv39_8f4b_R5_0_I1
  /\ Inv526_6f2c_R14_0_I1
  /\ Inv375_3bd9_R19_1_I1
  /\ Inv264_199a_R17_1_I1
  /\ Inv363_5241_R23_0_I2
  /\ Inv8_6351_R28_0_I1
  /\ Inv139_ec0b_R23_0_I2
  /\ Inv1056_5a8d_R2_2_I1
  /\ Inv63_dd88_R1_0_I2
  /\ Inv604_e925_R3_0_I1
  /\ Inv10_af7e_R3_1_I0
  /\ Inv4953_fa98_R1_1_I1
  /\ Inv2144_a275_R1_1_I1
  /\ Inv691_75d7_R1_2_I1


USE NType
USE maxClockType
USE DEF Count, Precedes

\* mean in-degree: 1.96875
\* median in-degree: 2
\* max in-degree: 6
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,RequestAction)
  <1>1. TypeOK /\ TypeOK /\ RequestAction => TypeOK' BY DEF TypeOK,RequestAction,Request,TypeOK
  \* (TypeOK,EnterAction)
  <1>2. TypeOK /\ TypeOK /\ EnterAction => TypeOK' BY DEF TypeOK,EnterAction,Enter,TypeOK,beats
  \* (TypeOK,ExitAction)
  <1>3. TypeOK /\ TypeOK /\ ExitAction => TypeOK' BY DEF TypeOK,ExitAction,Exit,TypeOK,beats,Broadcast
  \* (TypeOK,ReceiveRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ReceiveRequestAction => TypeOK' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,TypeOK
  \* (TypeOK,ReceiveAckAction)
  <1>5. TypeOK /\ TypeOK /\ ReceiveAckAction => TypeOK' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,TypeOK,beats
  \* (TypeOK,ReceiveReleaseAction)
  <1>6. TypeOK /\ TypeOK /\ ReceiveReleaseAction => TypeOK' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,TypeOK,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv13148_14cd_R0_0_I2 /\ Safety /\ Next => Safety'
  \* (Safety,RequestAction)
  <1>1. TypeOK /\ Safety /\ RequestAction => Safety' BY DEF TypeOK,RequestAction,Request,Safety,Mutex
  \* (Safety,EnterAction)
  <1>2. TypeOK /\ Inv13148_14cd_R0_0_I2 /\ Safety /\ EnterAction => Safety' BY DEF TypeOK,Inv13148_14cd_R0_0_I2,EnterAction,Enter,Safety,beats,Mutex
  \* (Safety,ExitAction)
  <1>3. TypeOK /\ Safety /\ ExitAction => Safety' BY DEF TypeOK,ExitAction,Exit,Safety,beats,Broadcast,Mutex
  \* (Safety,ReceiveRequestAction)
  <1>4. TypeOK /\ Safety /\ ReceiveRequestAction => Safety' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Safety,Mutex
  \* (Safety,ReceiveAckAction)
  <1>5. TypeOK /\ Safety /\ ReceiveAckAction => Safety' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Safety,beats,Mutex
  \* (Safety,ReceiveReleaseAction)
  <1>6. TypeOK /\ Safety /\ ReceiveReleaseAction => Safety' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Safety,beats,Mutex
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv13148_14cd_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv3213_dc35_R1_0_I2 /\ Inv63_dd88_R1_0_I2 /\ Inv357_3058_R1_3_I1 /\ Inv4953_fa98_R1_1_I1 /\ Inv2144_a275_R1_1_I1 /\ Inv691_75d7_R1_2_I1 /\ Inv13148_14cd_R0_0_I2 /\ Next => Inv13148_14cd_R0_0_I2'
  \* (Inv13148_14cd_R0_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv13148_14cd_R0_0_I2 /\ RequestAction => Inv13148_14cd_R0_0_I2' BY DEF TypeOK,RequestAction,Request,Inv13148_14cd_R0_0_I2
  \* (Inv13148_14cd_R0_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv3213_dc35_R1_0_I2 /\ Inv63_dd88_R1_0_I2 /\ Inv13148_14cd_R0_0_I2 /\ EnterAction => Inv13148_14cd_R0_0_I2' BY DEF TypeOK,Inv3213_dc35_R1_0_I2,Inv63_dd88_R1_0_I2,EnterAction,Enter,Inv13148_14cd_R0_0_I2,beats
  \* (Inv13148_14cd_R0_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv13148_14cd_R0_0_I2 /\ ExitAction => Inv13148_14cd_R0_0_I2' BY DEF TypeOK,ExitAction,Exit,Inv13148_14cd_R0_0_I2,beats,Broadcast
  \* (Inv13148_14cd_R0_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv13148_14cd_R0_0_I2 /\ ReceiveRequestAction => Inv13148_14cd_R0_0_I2' BY DEF TypeOK,Inv357_3058_R1_3_I1,ReceiveRequestAction,ReceiveRequest,Inv13148_14cd_R0_0_I2
  \* (Inv13148_14cd_R0_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv4953_fa98_R1_1_I1 /\ Inv2144_a275_R1_1_I1 /\ Inv13148_14cd_R0_0_I2 /\ ReceiveAckAction => Inv13148_14cd_R0_0_I2' BY DEF TypeOK,Inv4953_fa98_R1_1_I1,Inv2144_a275_R1_1_I1,ReceiveAckAction,ReceiveAck,Inv13148_14cd_R0_0_I2,beats
  \* (Inv13148_14cd_R0_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv691_75d7_R1_2_I1 /\ Inv13148_14cd_R0_0_I2 /\ ReceiveReleaseAction => Inv13148_14cd_R0_0_I2' BY DEF TypeOK,Inv691_75d7_R1_2_I1,ReceiveReleaseAction,ReceiveRelease,Inv13148_14cd_R0_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv3213_dc35_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv57_6f6e_R2_0_I1 /\ Inv1125_1f8c_R2_1_I1 /\ Inv1056_5a8d_R2_2_I1 /\ Inv3213_dc35_R1_0_I2 /\ Next => Inv3213_dc35_R1_0_I2'
  \* (Inv3213_dc35_R1_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv3213_dc35_R1_0_I2 /\ RequestAction => Inv3213_dc35_R1_0_I2' BY DEF TypeOK,RequestAction,Request,Inv3213_dc35_R1_0_I2
  \* (Inv3213_dc35_R1_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv3213_dc35_R1_0_I2 /\ EnterAction => Inv3213_dc35_R1_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv3213_dc35_R1_0_I2,beats
  \* (Inv3213_dc35_R1_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ Inv3213_dc35_R1_0_I2 /\ ExitAction => Inv3213_dc35_R1_0_I2' BY DEF TypeOK,Inv57_6f6e_R2_0_I1,ExitAction,Exit,Inv3213_dc35_R1_0_I2,beats,Broadcast
  \* (Inv3213_dc35_R1_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv3213_dc35_R1_0_I2 /\ ReceiveRequestAction => Inv3213_dc35_R1_0_I2' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv3213_dc35_R1_0_I2
  \* (Inv3213_dc35_R1_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ Inv3213_dc35_R1_0_I2 /\ ReceiveAckAction => Inv3213_dc35_R1_0_I2' BY DEF TypeOK,Inv1125_1f8c_R2_1_I1,ReceiveAckAction,ReceiveAck,Inv3213_dc35_R1_0_I2,beats
  \* (Inv3213_dc35_R1_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ Inv3213_dc35_R1_0_I2 /\ ReceiveReleaseAction => Inv3213_dc35_R1_0_I2' BY DEF TypeOK,Inv1056_5a8d_R2_2_I1,ReceiveReleaseAction,ReceiveRelease,Inv3213_dc35_R1_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv57_6f6e_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ Inv1056_5a8d_R2_2_I1 /\ Inv57_6f6e_R2_0_I1 /\ Next => Inv57_6f6e_R2_0_I1'
  \* (Inv57_6f6e_R2_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ RequestAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,RequestAction,Request,Inv57_6f6e_R2_0_I1
  \* (Inv57_6f6e_R2_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ EnterAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv57_6f6e_R2_0_I1,beats
  \* (Inv57_6f6e_R2_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ ExitAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv57_6f6e_R2_0_I1,beats,Broadcast
  \* (Inv57_6f6e_R2_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ ReceiveRequestAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv57_6f6e_R2_0_I1
  \* (Inv57_6f6e_R2_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ Inv57_6f6e_R2_0_I1 /\ ReceiveAckAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,Inv1125_1f8c_R2_1_I1,ReceiveAckAction,ReceiveAck,Inv57_6f6e_R2_0_I1,beats
  \* (Inv57_6f6e_R2_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ Inv57_6f6e_R2_0_I1 /\ ReceiveReleaseAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,Inv1056_5a8d_R2_2_I1,ReceiveReleaseAction,ReceiveRelease,Inv57_6f6e_R2_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1125_1f8c_R2_1_I1
THEOREM L_5 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv792_b5c0_R9_1_I1 /\ Inv1125_1f8c_R2_1_I1 /\ Next => Inv1125_1f8c_R2_1_I1'
  \* (Inv1125_1f8c_R2_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ RequestAction => Inv1125_1f8c_R2_1_I1' BY DEF TypeOK,RequestAction,Request,Inv1125_1f8c_R2_1_I1
  \* (Inv1125_1f8c_R2_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ EnterAction => Inv1125_1f8c_R2_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv1125_1f8c_R2_1_I1,beats
  \* (Inv1125_1f8c_R2_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv1125_1f8c_R2_1_I1 /\ ExitAction => Inv1125_1f8c_R2_1_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,ExitAction,Exit,Inv1125_1f8c_R2_1_I1,beats,Broadcast
  \* (Inv1125_1f8c_R2_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ ReceiveRequestAction => Inv1125_1f8c_R2_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1125_1f8c_R2_1_I1
  \* (Inv1125_1f8c_R2_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1125_1f8c_R2_1_I1 /\ ReceiveAckAction => Inv1125_1f8c_R2_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1125_1f8c_R2_1_I1,beats
  \* (Inv1125_1f8c_R2_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv792_b5c0_R9_1_I1 /\ Inv1125_1f8c_R2_1_I1 /\ ReceiveReleaseAction => Inv1125_1f8c_R2_1_I1' BY DEF TypeOK,Inv792_b5c0_R9_1_I1,ReceiveReleaseAction,ReceiveRelease,Inv1125_1f8c_R2_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv15_c48d_R4_0_I0
THEOREM L_6 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Next => Inv15_c48d_R4_0_I0'
  \* (Inv15_c48d_R4_0_I0,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ RequestAction => Inv15_c48d_R4_0_I0' BY DEF TypeOK,RequestAction,Request,Inv15_c48d_R4_0_I0
  \* (Inv15_c48d_R4_0_I0,EnterAction)
  <1>2. TypeOK /\ Inv15_c48d_R4_0_I0 /\ EnterAction => Inv15_c48d_R4_0_I0' BY DEF TypeOK,EnterAction,Enter,Inv15_c48d_R4_0_I0,beats
  \* (Inv15_c48d_R4_0_I0,ExitAction)
  <1>3. TypeOK /\ Inv15_c48d_R4_0_I0 /\ ExitAction => Inv15_c48d_R4_0_I0' BY DEF TypeOK,ExitAction,Exit,Inv15_c48d_R4_0_I0,beats,Broadcast
  \* (Inv15_c48d_R4_0_I0,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv15_c48d_R4_0_I0 /\ ReceiveRequestAction => Inv15_c48d_R4_0_I0' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv15_c48d_R4_0_I0
  \* (Inv15_c48d_R4_0_I0,ReceiveAckAction)
  <1>5. TypeOK /\ Inv15_c48d_R4_0_I0 /\ ReceiveAckAction => Inv15_c48d_R4_0_I0' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv15_c48d_R4_0_I0,beats
  \* (Inv15_c48d_R4_0_I0,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv15_c48d_R4_0_I0 /\ ReceiveReleaseAction => Inv15_c48d_R4_0_I0' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv15_c48d_R4_0_I0,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv792_b5c0_R9_1_I1
THEOREM L_7 == TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv264_199a_R17_1_I1 /\ Inv792_b5c0_R9_1_I1 /\ Next => Inv792_b5c0_R9_1_I1'
  \* (Inv792_b5c0_R9_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv792_b5c0_R9_1_I1 /\ RequestAction => Inv792_b5c0_R9_1_I1' BY DEF TypeOK,RequestAction,Request,Inv792_b5c0_R9_1_I1
  \* (Inv792_b5c0_R9_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv792_b5c0_R9_1_I1 /\ EnterAction => Inv792_b5c0_R9_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv792_b5c0_R9_1_I1,beats
  \* (Inv792_b5c0_R9_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv792_b5c0_R9_1_I1 /\ ExitAction => Inv792_b5c0_R9_1_I1' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv792_b5c0_R9_1_I1,beats,Broadcast
  \* (Inv792_b5c0_R9_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv264_199a_R17_1_I1 /\ Inv792_b5c0_R9_1_I1 /\ ReceiveRequestAction => Inv792_b5c0_R9_1_I1' BY DEF TypeOK,Inv264_199a_R17_1_I1,ReceiveRequestAction,ReceiveRequest,Inv792_b5c0_R9_1_I1
  \* (Inv792_b5c0_R9_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv792_b5c0_R9_1_I1 /\ ReceiveAckAction => Inv792_b5c0_R9_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv792_b5c0_R9_1_I1,beats
  \* (Inv792_b5c0_R9_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv792_b5c0_R9_1_I1 /\ ReceiveReleaseAction => Inv792_b5c0_R9_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv792_b5c0_R9_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv885_f510_R11_0_I1
THEOREM L_8 == TypeOK /\ Inv1072_3196_R18_0_I1 /\ Inv357_3058_R1_3_I1 /\ Inv885_f510_R11_0_I1 /\ Next => Inv885_f510_R11_0_I1'
  \* (Inv885_f510_R11_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv885_f510_R11_0_I1 /\ RequestAction => Inv885_f510_R11_0_I1' BY DEF TypeOK,RequestAction,Request,Inv885_f510_R11_0_I1
  \* (Inv885_f510_R11_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1072_3196_R18_0_I1 /\ Inv885_f510_R11_0_I1 /\ EnterAction => Inv885_f510_R11_0_I1' BY DEF TypeOK,Inv1072_3196_R18_0_I1,EnterAction,Enter,Inv885_f510_R11_0_I1,beats
  \* (Inv885_f510_R11_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ ExitAction => Inv885_f510_R11_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv885_f510_R11_0_I1,beats,Broadcast
  \* (Inv885_f510_R11_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv885_f510_R11_0_I1 /\ ReceiveRequestAction => Inv885_f510_R11_0_I1' BY DEF TypeOK,Inv357_3058_R1_3_I1,ReceiveRequestAction,ReceiveRequest,Inv885_f510_R11_0_I1
  \* (Inv885_f510_R11_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv885_f510_R11_0_I1 /\ ReceiveAckAction => Inv885_f510_R11_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv885_f510_R11_0_I1,beats
  \* (Inv885_f510_R11_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv885_f510_R11_0_I1 /\ ReceiveReleaseAction => Inv885_f510_R11_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv885_f510_R11_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1072_3196_R18_0_I1
THEOREM L_9 == TypeOK /\ Inv637_d0fa_R7_0_I1 /\ Inv73_44a3_R20_0_I1 /\ Inv363_5241_R23_0_I2 /\ Inv139_ec0b_R23_0_I2 /\ Inv1072_3196_R18_0_I1 /\ Next => Inv1072_3196_R18_0_I1'
  \* (Inv1072_3196_R18_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1072_3196_R18_0_I1 /\ RequestAction => Inv1072_3196_R18_0_I1' BY DEF TypeOK,RequestAction,Request,Inv1072_3196_R18_0_I1
  \* (Inv1072_3196_R18_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1072_3196_R18_0_I1 /\ EnterAction => Inv1072_3196_R18_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv1072_3196_R18_0_I1,beats
  \* (Inv1072_3196_R18_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv1072_3196_R18_0_I1 /\ ExitAction => Inv1072_3196_R18_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv1072_3196_R18_0_I1,beats,Broadcast
  \* (Inv1072_3196_R18_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ Inv1072_3196_R18_0_I1 /\ ReceiveRequestAction => Inv1072_3196_R18_0_I1' BY DEF TypeOK,Inv637_d0fa_R7_0_I1,ReceiveRequestAction,ReceiveRequest,Inv1072_3196_R18_0_I1
  \* (Inv1072_3196_R18_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv73_44a3_R20_0_I1 /\ Inv363_5241_R23_0_I2 /\ Inv139_ec0b_R23_0_I2 /\ Inv1072_3196_R18_0_I1 /\ ReceiveAckAction => Inv1072_3196_R18_0_I1' BY DEF TypeOK,Inv73_44a3_R20_0_I1,Inv363_5241_R23_0_I2,Inv139_ec0b_R23_0_I2,ReceiveAckAction,ReceiveAck,Inv1072_3196_R18_0_I1,beats
  \* (Inv1072_3196_R18_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1072_3196_R18_0_I1 /\ ReceiveReleaseAction => Inv1072_3196_R18_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1072_3196_R18_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv73_44a3_R20_0_I1
THEOREM L_10 == TypeOK /\ Inv1052_ce44_R21_1_I1 /\ Inv885_f510_R11_0_I1 /\ Inv2_3687_R21_0_I0 /\ Inv264_199a_R17_1_I1 /\ Inv73_44a3_R20_0_I1 /\ Next => Inv73_44a3_R20_0_I1'
  \* (Inv73_44a3_R20_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1052_ce44_R21_1_I1 /\ Inv73_44a3_R20_0_I1 /\ RequestAction => Inv73_44a3_R20_0_I1' BY DEF TypeOK,Inv1052_ce44_R21_1_I1,RequestAction,Request,Inv73_44a3_R20_0_I1
  \* (Inv73_44a3_R20_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv73_44a3_R20_0_I1 /\ EnterAction => Inv73_44a3_R20_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv73_44a3_R20_0_I1,beats
  \* (Inv73_44a3_R20_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv73_44a3_R20_0_I1 /\ ExitAction => Inv73_44a3_R20_0_I1' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv73_44a3_R20_0_I1,beats,Broadcast
  \* (Inv73_44a3_R20_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2_3687_R21_0_I0 /\ Inv264_199a_R17_1_I1 /\ Inv73_44a3_R20_0_I1 /\ ReceiveRequestAction => Inv73_44a3_R20_0_I1' BY DEF TypeOK,Inv2_3687_R21_0_I0,Inv264_199a_R17_1_I1,ReceiveRequestAction,ReceiveRequest,Inv73_44a3_R20_0_I1
  \* (Inv73_44a3_R20_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv73_44a3_R20_0_I1 /\ ReceiveAckAction => Inv73_44a3_R20_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv73_44a3_R20_0_I1,beats
  \* (Inv73_44a3_R20_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv73_44a3_R20_0_I1 /\ ReceiveReleaseAction => Inv73_44a3_R20_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv73_44a3_R20_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv2_3687_R21_0_I0
THEOREM L_11 == TypeOK /\ Inv997_9dba_R26_0_I1 /\ Inv2_3687_R21_0_I0 /\ Next => Inv2_3687_R21_0_I0'
  \* (Inv2_3687_R21_0_I0,RequestAction)
  <1>1. TypeOK /\ Inv997_9dba_R26_0_I1 /\ Inv2_3687_R21_0_I0 /\ RequestAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,Inv997_9dba_R26_0_I1,RequestAction,Request,Inv2_3687_R21_0_I0
  \* (Inv2_3687_R21_0_I0,EnterAction)
  <1>2. TypeOK /\ Inv2_3687_R21_0_I0 /\ EnterAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,EnterAction,Enter,Inv2_3687_R21_0_I0,beats
  \* (Inv2_3687_R21_0_I0,ExitAction)
  <1>3. TypeOK /\ Inv2_3687_R21_0_I0 /\ ExitAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,ExitAction,Exit,Inv2_3687_R21_0_I0,beats,Broadcast
  \* (Inv2_3687_R21_0_I0,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2_3687_R21_0_I0 /\ ReceiveRequestAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv2_3687_R21_0_I0
  \* (Inv2_3687_R21_0_I0,ReceiveAckAction)
  <1>5. TypeOK /\ Inv2_3687_R21_0_I0 /\ ReceiveAckAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv2_3687_R21_0_I0,beats
  \* (Inv2_3687_R21_0_I0,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv2_3687_R21_0_I0 /\ ReceiveReleaseAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv2_3687_R21_0_I0,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv997_9dba_R26_0_I1
THEOREM L_12 == TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv997_9dba_R26_0_I1 /\ Next => Inv997_9dba_R26_0_I1'
  \* (Inv997_9dba_R26_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv997_9dba_R26_0_I1 /\ RequestAction => Inv997_9dba_R26_0_I1' BY DEF TypeOK,RequestAction,Request,Inv997_9dba_R26_0_I1
  \* (Inv997_9dba_R26_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv997_9dba_R26_0_I1 /\ EnterAction => Inv997_9dba_R26_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv997_9dba_R26_0_I1,beats
  \* (Inv997_9dba_R26_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv997_9dba_R26_0_I1 /\ ExitAction => Inv997_9dba_R26_0_I1' BY DEF TypeOK,Inv357_3058_R1_3_I1,ExitAction,Exit,Inv997_9dba_R26_0_I1,beats,Broadcast
  \* (Inv997_9dba_R26_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv997_9dba_R26_0_I1 /\ ReceiveRequestAction => Inv997_9dba_R26_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv997_9dba_R26_0_I1
  \* (Inv997_9dba_R26_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv997_9dba_R26_0_I1 /\ ReceiveAckAction => Inv997_9dba_R26_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv997_9dba_R26_0_I1,beats
  \* (Inv997_9dba_R26_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv997_9dba_R26_0_I1 /\ ReceiveReleaseAction => Inv997_9dba_R26_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv997_9dba_R26_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv357_3058_R1_3_I1
THEOREM L_13 == TypeOK /\ Inv1703_12c5_R7_1_I1 /\ Inv637_d0fa_R7_0_I1 /\ Inv357_3058_R1_3_I1 /\ Next => Inv357_3058_R1_3_I1'
  \* (Inv357_3058_R1_3_I1,RequestAction)
  <1>1. TypeOK /\ Inv1703_12c5_R7_1_I1 /\ Inv357_3058_R1_3_I1 /\ RequestAction => Inv357_3058_R1_3_I1' BY DEF TypeOK,Inv1703_12c5_R7_1_I1,RequestAction,Request,Inv357_3058_R1_3_I1
  \* (Inv357_3058_R1_3_I1,EnterAction)
  <1>2. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ Inv357_3058_R1_3_I1 /\ EnterAction => Inv357_3058_R1_3_I1' BY DEF TypeOK,Inv637_d0fa_R7_0_I1,EnterAction,Enter,Inv357_3058_R1_3_I1,beats
  \* (Inv357_3058_R1_3_I1,ExitAction)
  <1>3. TypeOK /\ Inv357_3058_R1_3_I1 /\ ExitAction => Inv357_3058_R1_3_I1' BY DEF TypeOK,ExitAction,Exit,Inv357_3058_R1_3_I1,beats,Broadcast
  \* (Inv357_3058_R1_3_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv357_3058_R1_3_I1 /\ ReceiveRequestAction => Inv357_3058_R1_3_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv357_3058_R1_3_I1
  \* (Inv357_3058_R1_3_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv357_3058_R1_3_I1 /\ ReceiveAckAction => Inv357_3058_R1_3_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv357_3058_R1_3_I1,beats
  \* (Inv357_3058_R1_3_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv357_3058_R1_3_I1 /\ ReceiveReleaseAction => Inv357_3058_R1_3_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv357_3058_R1_3_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv637_d0fa_R7_0_I1
THEOREM L_14 == TypeOK /\ Inv168_a109_R15_0_I1 /\ Inv172_01bd_R15_0_I1 /\ Inv637_d0fa_R7_0_I1 /\ Next => Inv637_d0fa_R7_0_I1'
  \* (Inv637_d0fa_R7_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ RequestAction => Inv637_d0fa_R7_0_I1' BY DEF TypeOK,RequestAction,Request,Inv637_d0fa_R7_0_I1
  \* (Inv637_d0fa_R7_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ EnterAction => Inv637_d0fa_R7_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv637_d0fa_R7_0_I1,beats
  \* (Inv637_d0fa_R7_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ ExitAction => Inv637_d0fa_R7_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv637_d0fa_R7_0_I1,beats,Broadcast
  \* (Inv637_d0fa_R7_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ ReceiveRequestAction => Inv637_d0fa_R7_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv637_d0fa_R7_0_I1
  \* (Inv637_d0fa_R7_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv168_a109_R15_0_I1 /\ Inv172_01bd_R15_0_I1 /\ Inv637_d0fa_R7_0_I1 /\ ReceiveAckAction => Inv637_d0fa_R7_0_I1' BY DEF TypeOK,Inv168_a109_R15_0_I1,Inv172_01bd_R15_0_I1,ReceiveAckAction,ReceiveAck,Inv637_d0fa_R7_0_I1,beats
  \* (Inv637_d0fa_R7_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv637_d0fa_R7_0_I1 /\ ReceiveReleaseAction => Inv637_d0fa_R7_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv637_d0fa_R7_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv168_a109_R15_0_I1
THEOREM L_15 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv73_44a3_R20_0_I1 /\ Inv168_a109_R15_0_I1 /\ Next => Inv168_a109_R15_0_I1'
  \* (Inv168_a109_R15_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv168_a109_R15_0_I1 /\ RequestAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,RequestAction,Request,Inv168_a109_R15_0_I1
  \* (Inv168_a109_R15_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv168_a109_R15_0_I1 /\ EnterAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv168_a109_R15_0_I1,beats
  \* (Inv168_a109_R15_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv168_a109_R15_0_I1 /\ ExitAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv168_a109_R15_0_I1,beats,Broadcast
  \* (Inv168_a109_R15_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv168_a109_R15_0_I1 /\ ReceiveRequestAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv168_a109_R15_0_I1
  \* (Inv168_a109_R15_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv73_44a3_R20_0_I1 /\ Inv168_a109_R15_0_I1 /\ ReceiveAckAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,Inv73_44a3_R20_0_I1,ReceiveAckAction,ReceiveAck,Inv168_a109_R15_0_I1,beats
  \* (Inv168_a109_R15_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv168_a109_R15_0_I1 /\ ReceiveReleaseAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv168_a109_R15_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv172_01bd_R15_0_I1
THEOREM L_16 == TypeOK /\ Inv1052_ce44_R21_1_I1 /\ Inv2_3687_R21_0_I0 /\ Inv172_01bd_R15_0_I1 /\ Next => Inv172_01bd_R15_0_I1'
  \* (Inv172_01bd_R15_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1052_ce44_R21_1_I1 /\ Inv172_01bd_R15_0_I1 /\ RequestAction => Inv172_01bd_R15_0_I1' BY DEF TypeOK,Inv1052_ce44_R21_1_I1,RequestAction,Request,Inv172_01bd_R15_0_I1
  \* (Inv172_01bd_R15_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv172_01bd_R15_0_I1 /\ EnterAction => Inv172_01bd_R15_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv172_01bd_R15_0_I1,beats
  \* (Inv172_01bd_R15_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv172_01bd_R15_0_I1 /\ ExitAction => Inv172_01bd_R15_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv172_01bd_R15_0_I1,beats,Broadcast
  \* (Inv172_01bd_R15_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2_3687_R21_0_I0 /\ Inv172_01bd_R15_0_I1 /\ ReceiveRequestAction => Inv172_01bd_R15_0_I1' BY DEF TypeOK,Inv2_3687_R21_0_I0,ReceiveRequestAction,ReceiveRequest,Inv172_01bd_R15_0_I1
  \* (Inv172_01bd_R15_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv172_01bd_R15_0_I1 /\ ReceiveAckAction => Inv172_01bd_R15_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv172_01bd_R15_0_I1,beats
  \* (Inv172_01bd_R15_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv172_01bd_R15_0_I1 /\ ReceiveReleaseAction => Inv172_01bd_R15_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv172_01bd_R15_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1052_ce44_R21_1_I1
THEOREM L_17 == TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv997_9dba_R26_0_I1 /\ Inv1052_ce44_R21_1_I1 /\ Next => Inv1052_ce44_R21_1_I1'
  \* (Inv1052_ce44_R21_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv1052_ce44_R21_1_I1 /\ RequestAction => Inv1052_ce44_R21_1_I1' BY DEF TypeOK,RequestAction,Request,Inv1052_ce44_R21_1_I1
  \* (Inv1052_ce44_R21_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv1052_ce44_R21_1_I1 /\ EnterAction => Inv1052_ce44_R21_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv1052_ce44_R21_1_I1,beats
  \* (Inv1052_ce44_R21_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv1052_ce44_R21_1_I1 /\ ExitAction => Inv1052_ce44_R21_1_I1' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv1052_ce44_R21_1_I1,beats,Broadcast
  \* (Inv1052_ce44_R21_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv997_9dba_R26_0_I1 /\ Inv1052_ce44_R21_1_I1 /\ ReceiveRequestAction => Inv1052_ce44_R21_1_I1' BY DEF TypeOK,Inv997_9dba_R26_0_I1,ReceiveRequestAction,ReceiveRequest,Inv1052_ce44_R21_1_I1
  \* (Inv1052_ce44_R21_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1052_ce44_R21_1_I1 /\ ReceiveAckAction => Inv1052_ce44_R21_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1052_ce44_R21_1_I1,beats
  \* (Inv1052_ce44_R21_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1052_ce44_R21_1_I1 /\ ReceiveReleaseAction => Inv1052_ce44_R21_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1052_ce44_R21_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1703_12c5_R7_1_I1
THEOREM L_18 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv1703_12c5_R7_1_I1 /\ Next => Inv1703_12c5_R7_1_I1'
  \* (Inv1703_12c5_R7_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv1703_12c5_R7_1_I1 /\ RequestAction => Inv1703_12c5_R7_1_I1' BY DEF TypeOK,RequestAction,Request,Inv1703_12c5_R7_1_I1
  \* (Inv1703_12c5_R7_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv1703_12c5_R7_1_I1 /\ EnterAction => Inv1703_12c5_R7_1_I1' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,EnterAction,Enter,Inv1703_12c5_R7_1_I1,beats
  \* (Inv1703_12c5_R7_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv1703_12c5_R7_1_I1 /\ ExitAction => Inv1703_12c5_R7_1_I1' BY DEF TypeOK,ExitAction,Exit,Inv1703_12c5_R7_1_I1,beats,Broadcast
  \* (Inv1703_12c5_R7_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1703_12c5_R7_1_I1 /\ ReceiveRequestAction => Inv1703_12c5_R7_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1703_12c5_R7_1_I1
  \* (Inv1703_12c5_R7_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1703_12c5_R7_1_I1 /\ ReceiveAckAction => Inv1703_12c5_R7_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1703_12c5_R7_1_I1,beats
  \* (Inv1703_12c5_R7_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1703_12c5_R7_1_I1 /\ ReceiveReleaseAction => Inv1703_12c5_R7_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1703_12c5_R7_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv39_8f4b_R5_0_I1
THEOREM L_19 == TypeOK /\ Inv526_6f2c_R14_0_I1 /\ Inv39_8f4b_R5_0_I1 /\ Next => Inv39_8f4b_R5_0_I1'
  \* (Inv39_8f4b_R5_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ RequestAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,RequestAction,Request,Inv39_8f4b_R5_0_I1
  \* (Inv39_8f4b_R5_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ EnterAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv39_8f4b_R5_0_I1,beats
  \* (Inv39_8f4b_R5_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ ExitAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv39_8f4b_R5_0_I1,beats,Broadcast
  \* (Inv39_8f4b_R5_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ ReceiveRequestAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv39_8f4b_R5_0_I1
  \* (Inv39_8f4b_R5_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv526_6f2c_R14_0_I1 /\ Inv39_8f4b_R5_0_I1 /\ ReceiveAckAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,Inv526_6f2c_R14_0_I1,ReceiveAckAction,ReceiveAck,Inv39_8f4b_R5_0_I1,beats
  \* (Inv39_8f4b_R5_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ ReceiveReleaseAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv39_8f4b_R5_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv526_6f2c_R14_0_I1
THEOREM L_20 == TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv375_3bd9_R19_1_I1 /\ Inv526_6f2c_R14_0_I1 /\ Next => Inv526_6f2c_R14_0_I1'
  \* (Inv526_6f2c_R14_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv526_6f2c_R14_0_I1 /\ RequestAction => Inv526_6f2c_R14_0_I1' BY DEF TypeOK,RequestAction,Request,Inv526_6f2c_R14_0_I1
  \* (Inv526_6f2c_R14_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv526_6f2c_R14_0_I1 /\ EnterAction => Inv526_6f2c_R14_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv526_6f2c_R14_0_I1,beats
  \* (Inv526_6f2c_R14_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv526_6f2c_R14_0_I1 /\ ExitAction => Inv526_6f2c_R14_0_I1' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv526_6f2c_R14_0_I1,beats,Broadcast
  \* (Inv526_6f2c_R14_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv375_3bd9_R19_1_I1 /\ Inv526_6f2c_R14_0_I1 /\ ReceiveRequestAction => Inv526_6f2c_R14_0_I1' BY DEF TypeOK,Inv375_3bd9_R19_1_I1,ReceiveRequestAction,ReceiveRequest,Inv526_6f2c_R14_0_I1
  \* (Inv526_6f2c_R14_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv526_6f2c_R14_0_I1 /\ ReceiveAckAction => Inv526_6f2c_R14_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv526_6f2c_R14_0_I1,beats
  \* (Inv526_6f2c_R14_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv526_6f2c_R14_0_I1 /\ ReceiveReleaseAction => Inv526_6f2c_R14_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv526_6f2c_R14_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv375_3bd9_R19_1_I1
THEOREM L_21 == TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv375_3bd9_R19_1_I1 /\ Next => Inv375_3bd9_R19_1_I1'
  \* (Inv375_3bd9_R19_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv375_3bd9_R19_1_I1 /\ RequestAction => Inv375_3bd9_R19_1_I1' BY DEF TypeOK,RequestAction,Request,Inv375_3bd9_R19_1_I1
  \* (Inv375_3bd9_R19_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv375_3bd9_R19_1_I1 /\ EnterAction => Inv375_3bd9_R19_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv375_3bd9_R19_1_I1,beats
  \* (Inv375_3bd9_R19_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv375_3bd9_R19_1_I1 /\ ExitAction => Inv375_3bd9_R19_1_I1' BY DEF TypeOK,Inv357_3058_R1_3_I1,ExitAction,Exit,Inv375_3bd9_R19_1_I1,beats,Broadcast
  \* (Inv375_3bd9_R19_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv375_3bd9_R19_1_I1 /\ ReceiveRequestAction => Inv375_3bd9_R19_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv375_3bd9_R19_1_I1
  \* (Inv375_3bd9_R19_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv375_3bd9_R19_1_I1 /\ ReceiveAckAction => Inv375_3bd9_R19_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv375_3bd9_R19_1_I1,beats
  \* (Inv375_3bd9_R19_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv375_3bd9_R19_1_I1 /\ ReceiveReleaseAction => Inv375_3bd9_R19_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv375_3bd9_R19_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv264_199a_R17_1_I1
THEOREM L_22 == TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv264_199a_R17_1_I1 /\ Next => Inv264_199a_R17_1_I1'
  \* (Inv264_199a_R17_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv264_199a_R17_1_I1 /\ RequestAction => Inv264_199a_R17_1_I1' BY DEF TypeOK,RequestAction,Request,Inv264_199a_R17_1_I1
  \* (Inv264_199a_R17_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv264_199a_R17_1_I1 /\ EnterAction => Inv264_199a_R17_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv264_199a_R17_1_I1,beats
  \* (Inv264_199a_R17_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv264_199a_R17_1_I1 /\ ExitAction => Inv264_199a_R17_1_I1' BY DEF TypeOK,Inv357_3058_R1_3_I1,ExitAction,Exit,Inv264_199a_R17_1_I1,beats,Broadcast
  \* (Inv264_199a_R17_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv264_199a_R17_1_I1 /\ ReceiveRequestAction => Inv264_199a_R17_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv264_199a_R17_1_I1
  \* (Inv264_199a_R17_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv264_199a_R17_1_I1 /\ ReceiveAckAction => Inv264_199a_R17_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv264_199a_R17_1_I1,beats
  \* (Inv264_199a_R17_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv264_199a_R17_1_I1 /\ ReceiveReleaseAction => Inv264_199a_R17_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv264_199a_R17_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv363_5241_R23_0_I2
THEOREM L_23 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv168_a109_R15_0_I1 /\ Inv8_6351_R28_0_I1 /\ Inv363_5241_R23_0_I2 /\ Next => Inv363_5241_R23_0_I2'
  \* (Inv363_5241_R23_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv363_5241_R23_0_I2 /\ RequestAction => Inv363_5241_R23_0_I2' BY DEF TypeOK,Inv15_c48d_R4_0_I0,RequestAction,Request,Inv363_5241_R23_0_I2
  \* (Inv363_5241_R23_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv363_5241_R23_0_I2 /\ EnterAction => Inv363_5241_R23_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv363_5241_R23_0_I2,beats
  \* (Inv363_5241_R23_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv363_5241_R23_0_I2 /\ ExitAction => Inv363_5241_R23_0_I2' BY DEF TypeOK,ExitAction,Exit,Inv363_5241_R23_0_I2,beats,Broadcast
  \* (Inv363_5241_R23_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv168_a109_R15_0_I1 /\ Inv363_5241_R23_0_I2 /\ ReceiveRequestAction => Inv363_5241_R23_0_I2' BY DEF TypeOK,Inv168_a109_R15_0_I1,ReceiveRequestAction,ReceiveRequest,Inv363_5241_R23_0_I2
  \* (Inv363_5241_R23_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv8_6351_R28_0_I1 /\ Inv363_5241_R23_0_I2 /\ ReceiveAckAction => Inv363_5241_R23_0_I2' BY DEF TypeOK,Inv8_6351_R28_0_I1,ReceiveAckAction,ReceiveAck,Inv363_5241_R23_0_I2,beats
  \* (Inv363_5241_R23_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv363_5241_R23_0_I2 /\ ReceiveReleaseAction => Inv363_5241_R23_0_I2' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv363_5241_R23_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv8_6351_R28_0_I1
THEOREM L_24 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv885_f510_R11_0_I1 /\ Inv172_01bd_R15_0_I1 /\ Inv8_6351_R28_0_I1 /\ Next => Inv8_6351_R28_0_I1'
  \* (Inv8_6351_R28_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv8_6351_R28_0_I1 /\ RequestAction => Inv8_6351_R28_0_I1' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,RequestAction,Request,Inv8_6351_R28_0_I1
  \* (Inv8_6351_R28_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv8_6351_R28_0_I1 /\ EnterAction => Inv8_6351_R28_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv8_6351_R28_0_I1,beats
  \* (Inv8_6351_R28_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv8_6351_R28_0_I1 /\ ExitAction => Inv8_6351_R28_0_I1' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv8_6351_R28_0_I1,beats,Broadcast
  \* (Inv8_6351_R28_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv172_01bd_R15_0_I1 /\ Inv8_6351_R28_0_I1 /\ ReceiveRequestAction => Inv8_6351_R28_0_I1' BY DEF TypeOK,Inv172_01bd_R15_0_I1,ReceiveRequestAction,ReceiveRequest,Inv8_6351_R28_0_I1
  \* (Inv8_6351_R28_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv8_6351_R28_0_I1 /\ ReceiveAckAction => Inv8_6351_R28_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv8_6351_R28_0_I1,beats
  \* (Inv8_6351_R28_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv8_6351_R28_0_I1 /\ ReceiveReleaseAction => Inv8_6351_R28_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv8_6351_R28_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv139_ec0b_R23_0_I2
THEOREM L_25 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv885_f510_R11_0_I1 /\ Inv172_01bd_R15_0_I1 /\ Inv139_ec0b_R23_0_I2 /\ Next => Inv139_ec0b_R23_0_I2'
  \* (Inv139_ec0b_R23_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv139_ec0b_R23_0_I2 /\ RequestAction => Inv139_ec0b_R23_0_I2' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,RequestAction,Request,Inv139_ec0b_R23_0_I2
  \* (Inv139_ec0b_R23_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv139_ec0b_R23_0_I2 /\ EnterAction => Inv139_ec0b_R23_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv139_ec0b_R23_0_I2,beats
  \* (Inv139_ec0b_R23_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv139_ec0b_R23_0_I2 /\ ExitAction => Inv139_ec0b_R23_0_I2' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv139_ec0b_R23_0_I2,beats,Broadcast
  \* (Inv139_ec0b_R23_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv172_01bd_R15_0_I1 /\ Inv139_ec0b_R23_0_I2 /\ ReceiveRequestAction => Inv139_ec0b_R23_0_I2' BY DEF TypeOK,Inv172_01bd_R15_0_I1,ReceiveRequestAction,ReceiveRequest,Inv139_ec0b_R23_0_I2
  \* (Inv139_ec0b_R23_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv139_ec0b_R23_0_I2 /\ ReceiveAckAction => Inv139_ec0b_R23_0_I2' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv139_ec0b_R23_0_I2,beats
  \* (Inv139_ec0b_R23_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv139_ec0b_R23_0_I2 /\ ReceiveReleaseAction => Inv139_ec0b_R23_0_I2' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv139_ec0b_R23_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1056_5a8d_R2_2_I1
THEOREM L_26 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv792_b5c0_R9_1_I1 /\ Inv1056_5a8d_R2_2_I1 /\ Next => Inv1056_5a8d_R2_2_I1'
  \* (Inv1056_5a8d_R2_2_I1,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv1056_5a8d_R2_2_I1 /\ RequestAction => Inv1056_5a8d_R2_2_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,RequestAction,Request,Inv1056_5a8d_R2_2_I1
  \* (Inv1056_5a8d_R2_2_I1,EnterAction)
  <1>2. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ EnterAction => Inv1056_5a8d_R2_2_I1' BY DEF TypeOK,EnterAction,Enter,Inv1056_5a8d_R2_2_I1,beats
  \* (Inv1056_5a8d_R2_2_I1,ExitAction)
  <1>3. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ ExitAction => Inv1056_5a8d_R2_2_I1' BY DEF TypeOK,ExitAction,Exit,Inv1056_5a8d_R2_2_I1,beats,Broadcast
  \* (Inv1056_5a8d_R2_2_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ ReceiveRequestAction => Inv1056_5a8d_R2_2_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1056_5a8d_R2_2_I1
  \* (Inv1056_5a8d_R2_2_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv792_b5c0_R9_1_I1 /\ Inv1056_5a8d_R2_2_I1 /\ ReceiveAckAction => Inv1056_5a8d_R2_2_I1' BY DEF TypeOK,Inv792_b5c0_R9_1_I1,ReceiveAckAction,ReceiveAck,Inv1056_5a8d_R2_2_I1,beats
  \* (Inv1056_5a8d_R2_2_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ ReceiveReleaseAction => Inv1056_5a8d_R2_2_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1056_5a8d_R2_2_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv63_dd88_R1_0_I2
THEOREM L_27 == TypeOK /\ Inv10_af7e_R3_1_I0 /\ Inv604_e925_R3_0_I1 /\ Inv63_dd88_R1_0_I2 /\ Next => Inv63_dd88_R1_0_I2'
  \* (Inv63_dd88_R1_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv63_dd88_R1_0_I2 /\ RequestAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,RequestAction,Request,Inv63_dd88_R1_0_I2
  \* (Inv63_dd88_R1_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv63_dd88_R1_0_I2 /\ EnterAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv63_dd88_R1_0_I2,beats
  \* (Inv63_dd88_R1_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv63_dd88_R1_0_I2 /\ ExitAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,ExitAction,Exit,Inv63_dd88_R1_0_I2,beats,Broadcast
  \* (Inv63_dd88_R1_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv10_af7e_R3_1_I0 /\ Inv63_dd88_R1_0_I2 /\ ReceiveRequestAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,Inv10_af7e_R3_1_I0,ReceiveRequestAction,ReceiveRequest,Inv63_dd88_R1_0_I2
  \* (Inv63_dd88_R1_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv604_e925_R3_0_I1 /\ Inv63_dd88_R1_0_I2 /\ ReceiveAckAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,Inv604_e925_R3_0_I1,ReceiveAckAction,ReceiveAck,Inv63_dd88_R1_0_I2,beats
  \* (Inv63_dd88_R1_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv63_dd88_R1_0_I2 /\ ReceiveReleaseAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv63_dd88_R1_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv604_e925_R3_0_I1
THEOREM L_28 == TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv10_af7e_R3_1_I0 /\ Inv604_e925_R3_0_I1 /\ Next => Inv604_e925_R3_0_I1'
  \* (Inv604_e925_R3_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv604_e925_R3_0_I1 /\ RequestAction => Inv604_e925_R3_0_I1' BY DEF TypeOK,RequestAction,Request,Inv604_e925_R3_0_I1
  \* (Inv604_e925_R3_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv604_e925_R3_0_I1 /\ EnterAction => Inv604_e925_R3_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv604_e925_R3_0_I1,beats
  \* (Inv604_e925_R3_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv885_f510_R11_0_I1 /\ Inv604_e925_R3_0_I1 /\ ExitAction => Inv604_e925_R3_0_I1' BY DEF TypeOK,Inv885_f510_R11_0_I1,ExitAction,Exit,Inv604_e925_R3_0_I1,beats,Broadcast
  \* (Inv604_e925_R3_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv10_af7e_R3_1_I0 /\ Inv604_e925_R3_0_I1 /\ ReceiveRequestAction => Inv604_e925_R3_0_I1' BY DEF TypeOK,Inv10_af7e_R3_1_I0,ReceiveRequestAction,ReceiveRequest,Inv604_e925_R3_0_I1
  \* (Inv604_e925_R3_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv604_e925_R3_0_I1 /\ ReceiveAckAction => Inv604_e925_R3_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv604_e925_R3_0_I1,beats
  \* (Inv604_e925_R3_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv604_e925_R3_0_I1 /\ ReceiveReleaseAction => Inv604_e925_R3_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv604_e925_R3_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv10_af7e_R3_1_I0
THEOREM L_29 == TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv10_af7e_R3_1_I0 /\ Next => Inv10_af7e_R3_1_I0'
  \* (Inv10_af7e_R3_1_I0,RequestAction)
  <1>1. TypeOK /\ Inv10_af7e_R3_1_I0 /\ RequestAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,RequestAction,Request,Inv10_af7e_R3_1_I0
  \* (Inv10_af7e_R3_1_I0,EnterAction)
  <1>2. TypeOK /\ Inv10_af7e_R3_1_I0 /\ EnterAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,EnterAction,Enter,Inv10_af7e_R3_1_I0,beats
  \* (Inv10_af7e_R3_1_I0,ExitAction)
  <1>3. TypeOK /\ Inv357_3058_R1_3_I1 /\ Inv10_af7e_R3_1_I0 /\ ExitAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,Inv357_3058_R1_3_I1,ExitAction,Exit,Inv10_af7e_R3_1_I0,beats,Broadcast
  \* (Inv10_af7e_R3_1_I0,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv10_af7e_R3_1_I0 /\ ReceiveRequestAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv10_af7e_R3_1_I0
  \* (Inv10_af7e_R3_1_I0,ReceiveAckAction)
  <1>5. TypeOK /\ Inv10_af7e_R3_1_I0 /\ ReceiveAckAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv10_af7e_R3_1_I0,beats
  \* (Inv10_af7e_R3_1_I0,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv10_af7e_R3_1_I0 /\ ReceiveReleaseAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv10_af7e_R3_1_I0,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv4953_fa98_R1_1_I1
THEOREM L_30 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv4953_fa98_R1_1_I1 /\ Next => Inv4953_fa98_R1_1_I1'
  \* (Inv4953_fa98_R1_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv4953_fa98_R1_1_I1 /\ RequestAction => Inv4953_fa98_R1_1_I1' BY DEF TypeOK,RequestAction,Request,Inv4953_fa98_R1_1_I1
  \* (Inv4953_fa98_R1_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv4953_fa98_R1_1_I1 /\ EnterAction => Inv4953_fa98_R1_1_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,EnterAction,Enter,Inv4953_fa98_R1_1_I1,beats
  \* (Inv4953_fa98_R1_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv4953_fa98_R1_1_I1 /\ ExitAction => Inv4953_fa98_R1_1_I1' BY DEF TypeOK,ExitAction,Exit,Inv4953_fa98_R1_1_I1,beats,Broadcast
  \* (Inv4953_fa98_R1_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv4953_fa98_R1_1_I1 /\ ReceiveRequestAction => Inv4953_fa98_R1_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv4953_fa98_R1_1_I1
  \* (Inv4953_fa98_R1_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv4953_fa98_R1_1_I1 /\ ReceiveAckAction => Inv4953_fa98_R1_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv4953_fa98_R1_1_I1,beats
  \* (Inv4953_fa98_R1_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv4953_fa98_R1_1_I1 /\ ReceiveReleaseAction => Inv4953_fa98_R1_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv4953_fa98_R1_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv2144_a275_R1_1_I1
THEOREM L_31 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv2144_a275_R1_1_I1 /\ Next => Inv2144_a275_R1_1_I1'
  \* (Inv2144_a275_R1_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv2144_a275_R1_1_I1 /\ RequestAction => Inv2144_a275_R1_1_I1' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,RequestAction,Request,Inv2144_a275_R1_1_I1
  \* (Inv2144_a275_R1_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv2144_a275_R1_1_I1 /\ EnterAction => Inv2144_a275_R1_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv2144_a275_R1_1_I1,beats
  \* (Inv2144_a275_R1_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv2144_a275_R1_1_I1 /\ ExitAction => Inv2144_a275_R1_1_I1' BY DEF TypeOK,ExitAction,Exit,Inv2144_a275_R1_1_I1,beats,Broadcast
  \* (Inv2144_a275_R1_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2144_a275_R1_1_I1 /\ ReceiveRequestAction => Inv2144_a275_R1_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv2144_a275_R1_1_I1
  \* (Inv2144_a275_R1_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv2144_a275_R1_1_I1 /\ ReceiveAckAction => Inv2144_a275_R1_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv2144_a275_R1_1_I1,beats
  \* (Inv2144_a275_R1_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv2144_a275_R1_1_I1 /\ ReceiveReleaseAction => Inv2144_a275_R1_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv2144_a275_R1_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv691_75d7_R1_2_I1
THEOREM L_32 == TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ Inv691_75d7_R1_2_I1 /\ Next => Inv691_75d7_R1_2_I1'
  \* (Inv691_75d7_R1_2_I1,RequestAction)
  <1>1. TypeOK /\ Inv691_75d7_R1_2_I1 /\ RequestAction => Inv691_75d7_R1_2_I1' BY DEF TypeOK,RequestAction,Request,Inv691_75d7_R1_2_I1
  \* (Inv691_75d7_R1_2_I1,EnterAction)
  <1>2. TypeOK /\ Inv1056_5a8d_R2_2_I1 /\ Inv691_75d7_R1_2_I1 /\ EnterAction => Inv691_75d7_R1_2_I1' BY DEF TypeOK,Inv1056_5a8d_R2_2_I1,EnterAction,Enter,Inv691_75d7_R1_2_I1,beats
  \* (Inv691_75d7_R1_2_I1,ExitAction)
  <1>3. TypeOK /\ Inv691_75d7_R1_2_I1 /\ ExitAction => Inv691_75d7_R1_2_I1' BY DEF TypeOK,ExitAction,Exit,Inv691_75d7_R1_2_I1,beats,Broadcast
  \* (Inv691_75d7_R1_2_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv691_75d7_R1_2_I1 /\ ReceiveRequestAction => Inv691_75d7_R1_2_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv691_75d7_R1_2_I1
  \* (Inv691_75d7_R1_2_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv691_75d7_R1_2_I1 /\ ReceiveAckAction => Inv691_75d7_R1_2_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv691_75d7_R1_2_I1,beats
  \* (Inv691_75d7_R1_2_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv691_75d7_R1_2_I1 /\ ReceiveReleaseAction => Inv691_75d7_R1_2_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv691_75d7_R1_2_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv13148_14cd_R0_0_I2 BY DEF Init, Inv13148_14cd_R0_0_I2, IndGlobal
    <1>3. Init => Inv3213_dc35_R1_0_I2 BY DEF Init, Inv3213_dc35_R1_0_I2, IndGlobal
    <1>4. Init => Inv57_6f6e_R2_0_I1 BY DEF Init, Inv57_6f6e_R2_0_I1, IndGlobal
    <1>5. Init => Inv1125_1f8c_R2_1_I1 BY DEF Init, Inv1125_1f8c_R2_1_I1, IndGlobal
    <1>6. Init => Inv15_c48d_R4_0_I0 BY DEF Init, Inv15_c48d_R4_0_I0, IndGlobal
    <1>7. Init => Inv792_b5c0_R9_1_I1 BY DEF Init, Inv792_b5c0_R9_1_I1, IndGlobal
    <1>8. Init => Inv885_f510_R11_0_I1 BY DEF Init, Inv885_f510_R11_0_I1, IndGlobal
    <1>9. Init => Inv1072_3196_R18_0_I1 BY DEF Init, Inv1072_3196_R18_0_I1, IndGlobal
    <1>10. Init => Inv73_44a3_R20_0_I1 BY DEF Init, Inv73_44a3_R20_0_I1, IndGlobal
    <1>11. Init => Inv2_3687_R21_0_I0 BY DEF Init, Inv2_3687_R21_0_I0, IndGlobal
    <1>12. Init => Inv997_9dba_R26_0_I1 BY DEF Init, Inv997_9dba_R26_0_I1, IndGlobal
    <1>13. Init => Inv357_3058_R1_3_I1 BY DEF Init, Inv357_3058_R1_3_I1, IndGlobal
    <1>14. Init => Inv637_d0fa_R7_0_I1 BY DEF Init, Inv637_d0fa_R7_0_I1, IndGlobal
    <1>15. Init => Inv168_a109_R15_0_I1 BY DEF Init, Inv168_a109_R15_0_I1, IndGlobal
    <1>16. Init => Inv172_01bd_R15_0_I1 BY DEF Init, Inv172_01bd_R15_0_I1, IndGlobal
    <1>17. Init => Inv1052_ce44_R21_1_I1 BY DEF Init, Inv1052_ce44_R21_1_I1, IndGlobal
    <1>18. Init => Inv1703_12c5_R7_1_I1 BY DEF Init, Inv1703_12c5_R7_1_I1, IndGlobal
    <1>19. Init => Inv39_8f4b_R5_0_I1 BY DEF Init, Inv39_8f4b_R5_0_I1, IndGlobal
    <1>20. Init => Inv526_6f2c_R14_0_I1 BY DEF Init, Inv526_6f2c_R14_0_I1, IndGlobal
    <1>21. Init => Inv375_3bd9_R19_1_I1 BY DEF Init, Inv375_3bd9_R19_1_I1, IndGlobal
    <1>22. Init => Inv264_199a_R17_1_I1 BY DEF Init, Inv264_199a_R17_1_I1, IndGlobal
    <1>23. Init => Inv363_5241_R23_0_I2 BY DEF Init, Inv363_5241_R23_0_I2, IndGlobal
    <1>24. Init => Inv8_6351_R28_0_I1 BY DEF Init, Inv8_6351_R28_0_I1, IndGlobal
    <1>25. Init => Inv139_ec0b_R23_0_I2 BY DEF Init, Inv139_ec0b_R23_0_I2, IndGlobal
    <1>26. Init => Inv1056_5a8d_R2_2_I1 BY DEF Init, Inv1056_5a8d_R2_2_I1, IndGlobal
    <1>27. Init => Inv63_dd88_R1_0_I2 BY DEF Init, Inv63_dd88_R1_0_I2, IndGlobal
    <1>28. Init => Inv604_e925_R3_0_I1 BY DEF Init, Inv604_e925_R3_0_I1, IndGlobal
    <1>29. Init => Inv10_af7e_R3_1_I0 BY DEF Init, Inv10_af7e_R3_1_I0, IndGlobal
    <1>30. Init => Inv4953_fa98_R1_1_I1 BY DEF Init, Inv4953_fa98_R1_1_I1, IndGlobal
    <1>31. Init => Inv2144_a275_R1_1_I1 BY DEF Init, Inv2144_a275_R1_1_I1, IndGlobal
    <1>32. Init => Inv691_75d7_R1_2_I1 BY DEF Init, Inv691_75d7_R1_2_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32 DEF Next, IndGlobal

====