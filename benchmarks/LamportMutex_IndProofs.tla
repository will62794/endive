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
Inv14778_14cd_R0_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(beats(VARI,VARJ) /\ req = req)) \/ (~(ack[VARI] = Proc))
Inv3023_dc35_R1_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (VARI \in crit) \/ ((req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ])))
Inv63_dd88_R1_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv5351_fa98_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(network[VARI][VARI] # <<>>))
Inv2428_a275_R1_1_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
Inv686_7d37_R1_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "rel")) \/ (~(VARI \in crit))
Inv354_245d_R1_3_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "req")) \/ (~(VARI \in crit))
Inv57_6f6e_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
Inv1106_d0c9_R2_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(Contains(network[VARI][VARJ], "ack")))
Inv1052_a3d0_R2_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "rel")) \/ (~(VARJ \in ack[VARI]))
Inv603_da04_R3_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv10_af7e_R3_1_I0 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].clock > req[VARI][VARI])
Inv15_c48d_R4_0_I0 == \A VARI \in Proc : ~(network[VARI][VARI] # <<>>)
Inv39_8f4b_R5_0_I1 == \A VARI \in Proc : (ack[VARI] = {}) \/ ((req[VARI][VARI] > 0))
Inv637_2954_R7_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "req")) \/ (~(ack[VARI] = Proc))
Inv2204_12c5_R7_1_I1 == \A VARI \in Proc : (req[VARI][VARI] > 0) \/ (~(VARI \in crit))
Inv790_98d1_R9_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(Contains(network[VARJ][VARI], "rel")))
Inv883_765c_R11_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(VARJ \in crit))
Inv523_fc6b_R14_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARJ][VARI], "ack")) \/ (~(ack[VARI] = {}))
Inv168_a109_R15_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARJ \in ack[VARI]))
Inv172_849b_R15_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(Contains(network[VARJ][VARI], "req")))
Inv262_72d8_R17_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "rel")) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "req"))
Inv1067_2e56_R18_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARJ][VARI], "ack")) \/ (~(ack[VARI] = Proc))
Inv372_d6ca_R19_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "req")) \/ (~(ack[VARI] = {}))
Inv79_dabf_R20_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(Contains(network[VARJ][VARI], "ack")))
Inv2_3687_R21_0_I0 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "req") <= 1)
Inv1036_6109_R21_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARI] > 0) \/ (~(Contains(network[VARJ][VARI], "ack")))
Inv362_1b85_R23_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(Contains(network[VARI][VARJ], "ack")) \/ (~(VARI \in ack[VARJ]))
Inv3175_ec0b_R23_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "ack") <= 1) \/ ((VARI \in ack[VARJ]) \/ (~(network[VARI][VARJ] # <<>>)))
Inv997_f9fe_R26_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARI] > 0) \/ (~(Contains(network[VARI][VARJ], "req")))
Inv52_6351_R28_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (Count(network[VARI][VARJ], "ack") <= 1) \/ ((VARI \in ack[VARJ]))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv14778_14cd_R0_0_I2
  /\ Inv3023_dc35_R1_0_I2
  /\ Inv57_6f6e_R2_0_I1
  /\ Inv1106_d0c9_R2_1_I1
  /\ Inv15_c48d_R4_0_I0
  /\ Inv790_98d1_R9_1_I1
  /\ Inv883_765c_R11_0_I1
  /\ Inv1067_2e56_R18_0_I1
  /\ Inv79_dabf_R20_0_I1
  /\ Inv2_3687_R21_0_I0
  /\ Inv997_f9fe_R26_0_I1
  /\ Inv354_245d_R1_3_I1
  /\ Inv637_2954_R7_0_I1
  /\ Inv168_a109_R15_0_I1
  /\ Inv172_849b_R15_0_I1
  /\ Inv1036_6109_R21_1_I1
  /\ Inv2204_12c5_R7_1_I1
  /\ Inv39_8f4b_R5_0_I1
  /\ Inv523_fc6b_R14_0_I1
  /\ Inv372_d6ca_R19_1_I1
  /\ Inv262_72d8_R17_1_I1
  /\ Inv362_1b85_R23_0_I2
  /\ Inv52_6351_R28_0_I1
  /\ Inv3175_ec0b_R23_0_I2
  /\ Inv1052_a3d0_R2_2_I1
  /\ Inv63_dd88_R1_0_I2
  /\ Inv603_da04_R3_0_I1
  /\ Inv10_af7e_R3_1_I0
  /\ Inv5351_fa98_R1_1_I1
  /\ Inv2428_a275_R1_1_I1
  /\ Inv686_7d37_R1_2_I1


\* mean in-degree: 1.96875
\* median in-degree: 2
\* max in-degree: 6
\* min in-degree: 0
\* mean variable slice size: 0

USE NType
USE maxClockType
USE DEF Count, Precedes, Proc, Message, AckMessage, RelMessage, ReqMessage, Clock, Broadcast

ASSUME A1 == Nats \subseteq Nat
USE A1


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
THEOREM L_1 == TypeOK /\ Inv14778_14cd_R0_0_I2 /\ Safety /\ Next => Safety'
  \* (Safety,RequestAction)
  <1>1. TypeOK /\ Safety /\ RequestAction => Safety' BY DEF TypeOK,RequestAction,Request,Safety,Mutex
  \* (Safety,EnterAction)
  <1>2. TypeOK /\ Inv14778_14cd_R0_0_I2 /\ Safety /\ EnterAction => Safety' BY DEF TypeOK,Inv14778_14cd_R0_0_I2,EnterAction,Enter,Safety,beats,Mutex
  \* (Safety,ExitAction)
  <1>3. TypeOK /\ Safety /\ ExitAction => Safety' BY DEF TypeOK,ExitAction,Exit,Safety,beats,Broadcast,Mutex
  \* (Safety,ReceiveRequestAction)
  <1>4. TypeOK /\ Safety /\ ReceiveRequestAction => Safety' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Safety,Mutex
  \* (Safety,ReceiveAckAction)
  <1>5. TypeOK /\ Safety /\ ReceiveAckAction => Safety' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Safety,beats,Mutex
  \* (Safety,ReceiveReleaseAction)
  <1>6. TypeOK /\ Safety /\ ReceiveReleaseAction => Safety' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Safety,beats,Mutex
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv14778_14cd_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv3023_dc35_R1_0_I2 /\ Inv63_dd88_R1_0_I2 /\ Inv354_245d_R1_3_I1 /\ Inv5351_fa98_R1_1_I1 /\ Inv2428_a275_R1_1_I1 /\ Inv686_7d37_R1_2_I1 /\ Inv14778_14cd_R0_0_I2 /\ Next => Inv14778_14cd_R0_0_I2'
  \* (Inv14778_14cd_R0_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv14778_14cd_R0_0_I2 /\ RequestAction => Inv14778_14cd_R0_0_I2' BY DEF TypeOK,RequestAction,Request,Inv14778_14cd_R0_0_I2
  \* (Inv14778_14cd_R0_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv3023_dc35_R1_0_I2 /\ Inv63_dd88_R1_0_I2 /\ Inv14778_14cd_R0_0_I2 /\ EnterAction => Inv14778_14cd_R0_0_I2' BY DEF TypeOK,Inv3023_dc35_R1_0_I2,Inv63_dd88_R1_0_I2,EnterAction,Enter,Inv14778_14cd_R0_0_I2,beats
  \* (Inv14778_14cd_R0_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv14778_14cd_R0_0_I2 /\ ExitAction => Inv14778_14cd_R0_0_I2' BY DEF TypeOK,ExitAction,Exit,Inv14778_14cd_R0_0_I2,beats,Broadcast
  \* (Inv14778_14cd_R0_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv14778_14cd_R0_0_I2 /\ ReceiveRequestAction => Inv14778_14cd_R0_0_I2' BY DEF TypeOK,Inv354_245d_R1_3_I1,ReceiveRequestAction,ReceiveRequest,Inv14778_14cd_R0_0_I2
  \* (Inv14778_14cd_R0_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv5351_fa98_R1_1_I1 /\ Inv2428_a275_R1_1_I1 /\ Inv14778_14cd_R0_0_I2 /\ ReceiveAckAction => Inv14778_14cd_R0_0_I2' BY DEF TypeOK,Inv5351_fa98_R1_1_I1,Inv2428_a275_R1_1_I1,ReceiveAckAction,ReceiveAck,Inv14778_14cd_R0_0_I2,beats
  \* (Inv14778_14cd_R0_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv686_7d37_R1_2_I1 /\ Inv14778_14cd_R0_0_I2 /\ ReceiveReleaseAction => Inv14778_14cd_R0_0_I2' BY DEF TypeOK,Inv686_7d37_R1_2_I1,ReceiveReleaseAction,ReceiveRelease,Inv14778_14cd_R0_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv3023_dc35_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv57_6f6e_R2_0_I1 /\ Inv1106_d0c9_R2_1_I1 /\ Inv1052_a3d0_R2_2_I1 /\ Inv3023_dc35_R1_0_I2 /\ Next => Inv3023_dc35_R1_0_I2'
  \* (Inv3023_dc35_R1_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv3023_dc35_R1_0_I2 /\ RequestAction => Inv3023_dc35_R1_0_I2' BY DEF TypeOK,RequestAction,Request,Inv3023_dc35_R1_0_I2
  \* (Inv3023_dc35_R1_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv3023_dc35_R1_0_I2 /\ EnterAction => Inv3023_dc35_R1_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv3023_dc35_R1_0_I2,beats
  \* (Inv3023_dc35_R1_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ Inv3023_dc35_R1_0_I2 /\ ExitAction => Inv3023_dc35_R1_0_I2' BY DEF TypeOK,Inv57_6f6e_R2_0_I1,ExitAction,Exit,Inv3023_dc35_R1_0_I2,beats,Broadcast
  \* (Inv3023_dc35_R1_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv3023_dc35_R1_0_I2 /\ ReceiveRequestAction => Inv3023_dc35_R1_0_I2' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv3023_dc35_R1_0_I2
  \* (Inv3023_dc35_R1_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ Inv3023_dc35_R1_0_I2 /\ ReceiveAckAction => Inv3023_dc35_R1_0_I2' BY DEF TypeOK,Inv1106_d0c9_R2_1_I1,ReceiveAckAction,ReceiveAck,Inv3023_dc35_R1_0_I2,beats
  \* (Inv3023_dc35_R1_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ Inv3023_dc35_R1_0_I2 /\ ReceiveReleaseAction => Inv3023_dc35_R1_0_I2' BY DEF TypeOK,Inv1052_a3d0_R2_2_I1,ReceiveReleaseAction,ReceiveRelease,Inv3023_dc35_R1_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv57_6f6e_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ Inv1052_a3d0_R2_2_I1 /\ Inv57_6f6e_R2_0_I1 /\ Next => Inv57_6f6e_R2_0_I1'
  \* (Inv57_6f6e_R2_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ RequestAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,RequestAction,Request,Inv57_6f6e_R2_0_I1
  \* (Inv57_6f6e_R2_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ EnterAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv57_6f6e_R2_0_I1,beats
  \* (Inv57_6f6e_R2_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ ExitAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv57_6f6e_R2_0_I1,beats,Broadcast
  \* (Inv57_6f6e_R2_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv57_6f6e_R2_0_I1 /\ ReceiveRequestAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv57_6f6e_R2_0_I1
  \* (Inv57_6f6e_R2_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ Inv57_6f6e_R2_0_I1 /\ ReceiveAckAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,Inv1106_d0c9_R2_1_I1,ReceiveAckAction,ReceiveAck,Inv57_6f6e_R2_0_I1,beats
  \* (Inv57_6f6e_R2_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ Inv57_6f6e_R2_0_I1 /\ ReceiveReleaseAction => Inv57_6f6e_R2_0_I1' BY DEF TypeOK,Inv1052_a3d0_R2_2_I1,ReceiveReleaseAction,ReceiveRelease,Inv57_6f6e_R2_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1106_d0c9_R2_1_I1
THEOREM L_5 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv790_98d1_R9_1_I1 /\ Inv1106_d0c9_R2_1_I1 /\ Next => Inv1106_d0c9_R2_1_I1'
  \* (Inv1106_d0c9_R2_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ RequestAction => Inv1106_d0c9_R2_1_I1' BY DEF TypeOK,RequestAction,Request,Inv1106_d0c9_R2_1_I1
  \* (Inv1106_d0c9_R2_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ EnterAction => Inv1106_d0c9_R2_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv1106_d0c9_R2_1_I1,beats
  \* (Inv1106_d0c9_R2_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv1106_d0c9_R2_1_I1 /\ ExitAction => Inv1106_d0c9_R2_1_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,ExitAction,Exit,Inv1106_d0c9_R2_1_I1,beats,Broadcast
  \* (Inv1106_d0c9_R2_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ ReceiveRequestAction => Inv1106_d0c9_R2_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1106_d0c9_R2_1_I1
  \* (Inv1106_d0c9_R2_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1106_d0c9_R2_1_I1 /\ ReceiveAckAction => Inv1106_d0c9_R2_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1106_d0c9_R2_1_I1,beats
  \* (Inv1106_d0c9_R2_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv790_98d1_R9_1_I1 /\ Inv1106_d0c9_R2_1_I1 /\ ReceiveReleaseAction => Inv1106_d0c9_R2_1_I1' BY DEF TypeOK,Inv790_98d1_R9_1_I1,ReceiveReleaseAction,ReceiveRelease,Inv1106_d0c9_R2_1_I1,beats
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


\*** Inv790_98d1_R9_1_I1
THEOREM L_7 == TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv262_72d8_R17_1_I1 /\ Inv790_98d1_R9_1_I1 /\ Next => Inv790_98d1_R9_1_I1'
  \* (Inv790_98d1_R9_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv790_98d1_R9_1_I1 /\ RequestAction => Inv790_98d1_R9_1_I1' BY DEF TypeOK,RequestAction,Request,Inv790_98d1_R9_1_I1
  \* (Inv790_98d1_R9_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv790_98d1_R9_1_I1 /\ EnterAction => Inv790_98d1_R9_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv790_98d1_R9_1_I1,beats
  \* (Inv790_98d1_R9_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv790_98d1_R9_1_I1 /\ ExitAction => Inv790_98d1_R9_1_I1' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv790_98d1_R9_1_I1,beats,Broadcast
  \* (Inv790_98d1_R9_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv262_72d8_R17_1_I1 /\ Inv790_98d1_R9_1_I1 /\ ReceiveRequestAction => Inv790_98d1_R9_1_I1' BY DEF TypeOK,Inv262_72d8_R17_1_I1,ReceiveRequestAction,ReceiveRequest,Inv790_98d1_R9_1_I1
  \* (Inv790_98d1_R9_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv790_98d1_R9_1_I1 /\ ReceiveAckAction => Inv790_98d1_R9_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv790_98d1_R9_1_I1,beats
  \* (Inv790_98d1_R9_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv790_98d1_R9_1_I1 /\ ReceiveReleaseAction => Inv790_98d1_R9_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv790_98d1_R9_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv883_765c_R11_0_I1
THEOREM L_8 == TypeOK /\ Inv1067_2e56_R18_0_I1 /\ Inv354_245d_R1_3_I1 /\ Inv883_765c_R11_0_I1 /\ Next => Inv883_765c_R11_0_I1'
  \* (Inv883_765c_R11_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv883_765c_R11_0_I1 /\ RequestAction => Inv883_765c_R11_0_I1' BY DEF TypeOK,RequestAction,Request,Inv883_765c_R11_0_I1
  \* (Inv883_765c_R11_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1067_2e56_R18_0_I1 /\ Inv883_765c_R11_0_I1 /\ EnterAction => Inv883_765c_R11_0_I1' BY DEF TypeOK,Inv1067_2e56_R18_0_I1,EnterAction,Enter,Inv883_765c_R11_0_I1,beats
  \* (Inv883_765c_R11_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ ExitAction => Inv883_765c_R11_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv883_765c_R11_0_I1,beats,Broadcast
  \* (Inv883_765c_R11_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv883_765c_R11_0_I1 /\ ReceiveRequestAction => Inv883_765c_R11_0_I1' BY DEF TypeOK,Inv354_245d_R1_3_I1,ReceiveRequestAction,ReceiveRequest,Inv883_765c_R11_0_I1
  \* (Inv883_765c_R11_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv883_765c_R11_0_I1 /\ ReceiveAckAction => Inv883_765c_R11_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv883_765c_R11_0_I1,beats
  \* (Inv883_765c_R11_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv883_765c_R11_0_I1 /\ ReceiveReleaseAction => Inv883_765c_R11_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv883_765c_R11_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1067_2e56_R18_0_I1
THEOREM L_9 == TypeOK /\ Inv637_2954_R7_0_I1 /\ Inv79_dabf_R20_0_I1 /\ Inv362_1b85_R23_0_I2 /\ Inv3175_ec0b_R23_0_I2 /\ Inv1067_2e56_R18_0_I1 /\ Next => Inv1067_2e56_R18_0_I1'
  \* (Inv1067_2e56_R18_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1067_2e56_R18_0_I1 /\ RequestAction => Inv1067_2e56_R18_0_I1' BY DEF TypeOK,RequestAction,Request,Inv1067_2e56_R18_0_I1
  \* (Inv1067_2e56_R18_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1067_2e56_R18_0_I1 /\ EnterAction => Inv1067_2e56_R18_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv1067_2e56_R18_0_I1,beats
  \* (Inv1067_2e56_R18_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv1067_2e56_R18_0_I1 /\ ExitAction => Inv1067_2e56_R18_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv1067_2e56_R18_0_I1,beats,Broadcast
  \* (Inv1067_2e56_R18_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv637_2954_R7_0_I1 /\ Inv1067_2e56_R18_0_I1 /\ ReceiveRequestAction => Inv1067_2e56_R18_0_I1' BY DEF TypeOK,Inv637_2954_R7_0_I1,ReceiveRequestAction,ReceiveRequest,Inv1067_2e56_R18_0_I1
  \* (Inv1067_2e56_R18_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv79_dabf_R20_0_I1 /\ Inv362_1b85_R23_0_I2 /\ Inv3175_ec0b_R23_0_I2 /\ Inv1067_2e56_R18_0_I1 /\ ReceiveAckAction => Inv1067_2e56_R18_0_I1' BY DEF TypeOK,Inv79_dabf_R20_0_I1,Inv362_1b85_R23_0_I2,Inv3175_ec0b_R23_0_I2,ReceiveAckAction,ReceiveAck,Inv1067_2e56_R18_0_I1,beats
  \* (Inv1067_2e56_R18_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1067_2e56_R18_0_I1 /\ ReceiveReleaseAction => Inv1067_2e56_R18_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1067_2e56_R18_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv79_dabf_R20_0_I1
THEOREM L_10 == TypeOK /\ Inv1036_6109_R21_1_I1 /\ Inv883_765c_R11_0_I1 /\ Inv2_3687_R21_0_I0 /\ Inv262_72d8_R17_1_I1 /\ Inv79_dabf_R20_0_I1 /\ Next => Inv79_dabf_R20_0_I1'
  \* (Inv79_dabf_R20_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1036_6109_R21_1_I1 /\ Inv79_dabf_R20_0_I1 /\ RequestAction => Inv79_dabf_R20_0_I1' BY DEF TypeOK,Inv1036_6109_R21_1_I1,RequestAction,Request,Inv79_dabf_R20_0_I1
  \* (Inv79_dabf_R20_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv79_dabf_R20_0_I1 /\ EnterAction => Inv79_dabf_R20_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv79_dabf_R20_0_I1,beats
  \* (Inv79_dabf_R20_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv79_dabf_R20_0_I1 /\ ExitAction => Inv79_dabf_R20_0_I1' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv79_dabf_R20_0_I1,beats,Broadcast
  \* (Inv79_dabf_R20_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2_3687_R21_0_I0 /\ Inv262_72d8_R17_1_I1 /\ Inv79_dabf_R20_0_I1 /\ ReceiveRequestAction => Inv79_dabf_R20_0_I1' BY DEF TypeOK,Inv2_3687_R21_0_I0,Inv262_72d8_R17_1_I1,ReceiveRequestAction,ReceiveRequest,Inv79_dabf_R20_0_I1
  \* (Inv79_dabf_R20_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv79_dabf_R20_0_I1 /\ ReceiveAckAction => Inv79_dabf_R20_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv79_dabf_R20_0_I1,beats
  \* (Inv79_dabf_R20_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv79_dabf_R20_0_I1 /\ ReceiveReleaseAction => Inv79_dabf_R20_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv79_dabf_R20_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv2_3687_R21_0_I0
THEOREM L_11 == TypeOK /\ Inv997_f9fe_R26_0_I1 /\ Inv2_3687_R21_0_I0 /\ Next => Inv2_3687_R21_0_I0'
  \* (Inv2_3687_R21_0_I0,RequestAction)
  <1>1. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ Inv2_3687_R21_0_I0 /\ RequestAction => Inv2_3687_R21_0_I0' BY DEF TypeOK,Inv997_f9fe_R26_0_I1,RequestAction,Request,Inv2_3687_R21_0_I0
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


\*** Inv997_f9fe_R26_0_I1
THEOREM L_12 == TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv997_f9fe_R26_0_I1 /\ Next => Inv997_f9fe_R26_0_I1'
  \* (Inv997_f9fe_R26_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ RequestAction => Inv997_f9fe_R26_0_I1' BY DEF TypeOK,RequestAction,Request,Inv997_f9fe_R26_0_I1
  \* (Inv997_f9fe_R26_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ EnterAction => Inv997_f9fe_R26_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv997_f9fe_R26_0_I1,beats
  \* (Inv997_f9fe_R26_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv997_f9fe_R26_0_I1 /\ ExitAction => Inv997_f9fe_R26_0_I1' BY DEF TypeOK,Inv354_245d_R1_3_I1,ExitAction,Exit,Inv997_f9fe_R26_0_I1,beats,Broadcast
  \* (Inv997_f9fe_R26_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ ReceiveRequestAction => Inv997_f9fe_R26_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv997_f9fe_R26_0_I1
  \* (Inv997_f9fe_R26_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ ReceiveAckAction => Inv997_f9fe_R26_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv997_f9fe_R26_0_I1,beats
  \* (Inv997_f9fe_R26_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ ReceiveReleaseAction => Inv997_f9fe_R26_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv997_f9fe_R26_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv354_245d_R1_3_I1
THEOREM L_13 == TypeOK /\ Inv2204_12c5_R7_1_I1 /\ Inv637_2954_R7_0_I1 /\ Inv354_245d_R1_3_I1 /\ Next => Inv354_245d_R1_3_I1'
  \* (Inv354_245d_R1_3_I1,RequestAction)
  <1>1. TypeOK /\ Inv2204_12c5_R7_1_I1 /\ Inv354_245d_R1_3_I1 /\ RequestAction => Inv354_245d_R1_3_I1' BY DEF TypeOK,Inv2204_12c5_R7_1_I1,RequestAction,Request,Inv354_245d_R1_3_I1
  \* (Inv354_245d_R1_3_I1,EnterAction)
  <1>2. TypeOK /\ Inv637_2954_R7_0_I1 /\ Inv354_245d_R1_3_I1 /\ EnterAction => Inv354_245d_R1_3_I1' BY DEF TypeOK,Inv637_2954_R7_0_I1,EnterAction,Enter,Inv354_245d_R1_3_I1,beats
  \* (Inv354_245d_R1_3_I1,ExitAction)
  <1>3. TypeOK /\ Inv354_245d_R1_3_I1 /\ ExitAction => Inv354_245d_R1_3_I1' BY DEF TypeOK,ExitAction,Exit,Inv354_245d_R1_3_I1,beats,Broadcast
  \* (Inv354_245d_R1_3_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv354_245d_R1_3_I1 /\ ReceiveRequestAction => Inv354_245d_R1_3_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv354_245d_R1_3_I1
  \* (Inv354_245d_R1_3_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv354_245d_R1_3_I1 /\ ReceiveAckAction => Inv354_245d_R1_3_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv354_245d_R1_3_I1,beats
  \* (Inv354_245d_R1_3_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv354_245d_R1_3_I1 /\ ReceiveReleaseAction => Inv354_245d_R1_3_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv354_245d_R1_3_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv637_2954_R7_0_I1
THEOREM L_14 == TypeOK /\ Inv168_a109_R15_0_I1 /\ Inv172_849b_R15_0_I1 /\ Inv637_2954_R7_0_I1 /\ Next => Inv637_2954_R7_0_I1'
  \* (Inv637_2954_R7_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv637_2954_R7_0_I1 /\ RequestAction => Inv637_2954_R7_0_I1' BY DEF TypeOK,RequestAction,Request,Inv637_2954_R7_0_I1
  \* (Inv637_2954_R7_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv637_2954_R7_0_I1 /\ EnterAction => Inv637_2954_R7_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv637_2954_R7_0_I1,beats
  \* (Inv637_2954_R7_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv637_2954_R7_0_I1 /\ ExitAction => Inv637_2954_R7_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv637_2954_R7_0_I1,beats,Broadcast
  \* (Inv637_2954_R7_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv637_2954_R7_0_I1 /\ ReceiveRequestAction => Inv637_2954_R7_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv637_2954_R7_0_I1
  \* (Inv637_2954_R7_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv168_a109_R15_0_I1 /\ Inv172_849b_R15_0_I1 /\ Inv637_2954_R7_0_I1 /\ ReceiveAckAction => Inv637_2954_R7_0_I1' BY DEF TypeOK,Inv168_a109_R15_0_I1,Inv172_849b_R15_0_I1,ReceiveAckAction,ReceiveAck,Inv637_2954_R7_0_I1,beats
  \* (Inv637_2954_R7_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv637_2954_R7_0_I1 /\ ReceiveReleaseAction => Inv637_2954_R7_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv637_2954_R7_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv168_a109_R15_0_I1
THEOREM L_15 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv79_dabf_R20_0_I1 /\ Inv168_a109_R15_0_I1 /\ Next => Inv168_a109_R15_0_I1'
  \* (Inv168_a109_R15_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv168_a109_R15_0_I1 /\ RequestAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,RequestAction,Request,Inv168_a109_R15_0_I1
  \* (Inv168_a109_R15_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv168_a109_R15_0_I1 /\ EnterAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv168_a109_R15_0_I1,beats
  \* (Inv168_a109_R15_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv168_a109_R15_0_I1 /\ ExitAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv168_a109_R15_0_I1,beats,Broadcast
  \* (Inv168_a109_R15_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv168_a109_R15_0_I1 /\ ReceiveRequestAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv168_a109_R15_0_I1
  \* (Inv168_a109_R15_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv79_dabf_R20_0_I1 /\ Inv168_a109_R15_0_I1 /\ ReceiveAckAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,Inv79_dabf_R20_0_I1,ReceiveAckAction,ReceiveAck,Inv168_a109_R15_0_I1,beats
  \* (Inv168_a109_R15_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv168_a109_R15_0_I1 /\ ReceiveReleaseAction => Inv168_a109_R15_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv168_a109_R15_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv172_849b_R15_0_I1
THEOREM L_16 == TypeOK /\ Inv1036_6109_R21_1_I1 /\ Inv2_3687_R21_0_I0 /\ Inv172_849b_R15_0_I1 /\ Next => Inv172_849b_R15_0_I1'
  \* (Inv172_849b_R15_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1036_6109_R21_1_I1 /\ Inv172_849b_R15_0_I1 /\ RequestAction => Inv172_849b_R15_0_I1' BY DEF TypeOK,Inv1036_6109_R21_1_I1,RequestAction,Request,Inv172_849b_R15_0_I1
  \* (Inv172_849b_R15_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv172_849b_R15_0_I1 /\ EnterAction => Inv172_849b_R15_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv172_849b_R15_0_I1,beats
  \* (Inv172_849b_R15_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv172_849b_R15_0_I1 /\ ExitAction => Inv172_849b_R15_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv172_849b_R15_0_I1,beats,Broadcast
  \* (Inv172_849b_R15_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2_3687_R21_0_I0 /\ Inv172_849b_R15_0_I1 /\ ReceiveRequestAction => Inv172_849b_R15_0_I1' BY DEF TypeOK,Inv2_3687_R21_0_I0,ReceiveRequestAction,ReceiveRequest,Inv172_849b_R15_0_I1
  \* (Inv172_849b_R15_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv172_849b_R15_0_I1 /\ ReceiveAckAction => Inv172_849b_R15_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv172_849b_R15_0_I1,beats
  \* (Inv172_849b_R15_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv172_849b_R15_0_I1 /\ ReceiveReleaseAction => Inv172_849b_R15_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv172_849b_R15_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1036_6109_R21_1_I1
THEOREM L_17 == TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv997_f9fe_R26_0_I1 /\ Inv1036_6109_R21_1_I1 /\ Next => Inv1036_6109_R21_1_I1'
  \* (Inv1036_6109_R21_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv1036_6109_R21_1_I1 /\ RequestAction => Inv1036_6109_R21_1_I1' BY DEF TypeOK,RequestAction,Request,Inv1036_6109_R21_1_I1
  \* (Inv1036_6109_R21_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv1036_6109_R21_1_I1 /\ EnterAction => Inv1036_6109_R21_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv1036_6109_R21_1_I1,beats
  \* (Inv1036_6109_R21_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv1036_6109_R21_1_I1 /\ ExitAction => Inv1036_6109_R21_1_I1' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv1036_6109_R21_1_I1,beats,Broadcast
  \* (Inv1036_6109_R21_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv997_f9fe_R26_0_I1 /\ Inv1036_6109_R21_1_I1 /\ ReceiveRequestAction => Inv1036_6109_R21_1_I1' BY DEF TypeOK,Inv997_f9fe_R26_0_I1,ReceiveRequestAction,ReceiveRequest,Inv1036_6109_R21_1_I1
  \* (Inv1036_6109_R21_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1036_6109_R21_1_I1 /\ ReceiveAckAction => Inv1036_6109_R21_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1036_6109_R21_1_I1,beats
  \* (Inv1036_6109_R21_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1036_6109_R21_1_I1 /\ ReceiveReleaseAction => Inv1036_6109_R21_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1036_6109_R21_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv2204_12c5_R7_1_I1
THEOREM L_18 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv2204_12c5_R7_1_I1 /\ Next => Inv2204_12c5_R7_1_I1'
  \* (Inv2204_12c5_R7_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv2204_12c5_R7_1_I1 /\ RequestAction => Inv2204_12c5_R7_1_I1' BY DEF TypeOK,RequestAction,Request,Inv2204_12c5_R7_1_I1
  \* (Inv2204_12c5_R7_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv2204_12c5_R7_1_I1 /\ EnterAction => Inv2204_12c5_R7_1_I1' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,EnterAction,Enter,Inv2204_12c5_R7_1_I1,beats
  \* (Inv2204_12c5_R7_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv2204_12c5_R7_1_I1 /\ ExitAction => Inv2204_12c5_R7_1_I1' BY DEF TypeOK,ExitAction,Exit,Inv2204_12c5_R7_1_I1,beats,Broadcast
  \* (Inv2204_12c5_R7_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2204_12c5_R7_1_I1 /\ ReceiveRequestAction => Inv2204_12c5_R7_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv2204_12c5_R7_1_I1
  \* (Inv2204_12c5_R7_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv2204_12c5_R7_1_I1 /\ ReceiveAckAction => Inv2204_12c5_R7_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv2204_12c5_R7_1_I1,beats
  \* (Inv2204_12c5_R7_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv2204_12c5_R7_1_I1 /\ ReceiveReleaseAction => Inv2204_12c5_R7_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv2204_12c5_R7_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv39_8f4b_R5_0_I1
THEOREM L_19 == TypeOK /\ Inv523_fc6b_R14_0_I1 /\ Inv39_8f4b_R5_0_I1 /\ Next => Inv39_8f4b_R5_0_I1'
  \* (Inv39_8f4b_R5_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ RequestAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,RequestAction,Request,Inv39_8f4b_R5_0_I1
  \* (Inv39_8f4b_R5_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ EnterAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv39_8f4b_R5_0_I1,beats
  \* (Inv39_8f4b_R5_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ ExitAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,ExitAction,Exit,Inv39_8f4b_R5_0_I1,beats,Broadcast
  \* (Inv39_8f4b_R5_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ ReceiveRequestAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv39_8f4b_R5_0_I1
  \* (Inv39_8f4b_R5_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv523_fc6b_R14_0_I1 /\ Inv39_8f4b_R5_0_I1 /\ ReceiveAckAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,Inv523_fc6b_R14_0_I1,ReceiveAckAction,ReceiveAck,Inv39_8f4b_R5_0_I1,beats
  \* (Inv39_8f4b_R5_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ ReceiveReleaseAction => Inv39_8f4b_R5_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv39_8f4b_R5_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv523_fc6b_R14_0_I1
THEOREM L_20 == TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv372_d6ca_R19_1_I1 /\ Inv523_fc6b_R14_0_I1 /\ Next => Inv523_fc6b_R14_0_I1'
  \* (Inv523_fc6b_R14_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv523_fc6b_R14_0_I1 /\ RequestAction => Inv523_fc6b_R14_0_I1' BY DEF TypeOK,RequestAction,Request,Inv523_fc6b_R14_0_I1
  \* (Inv523_fc6b_R14_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv523_fc6b_R14_0_I1 /\ EnterAction => Inv523_fc6b_R14_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv523_fc6b_R14_0_I1,beats
  \* (Inv523_fc6b_R14_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv523_fc6b_R14_0_I1 /\ ExitAction => Inv523_fc6b_R14_0_I1' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv523_fc6b_R14_0_I1,beats,Broadcast
  \* (Inv523_fc6b_R14_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv372_d6ca_R19_1_I1 /\ Inv523_fc6b_R14_0_I1 /\ ReceiveRequestAction => Inv523_fc6b_R14_0_I1' BY DEF TypeOK,Inv372_d6ca_R19_1_I1,ReceiveRequestAction,ReceiveRequest,Inv523_fc6b_R14_0_I1
  \* (Inv523_fc6b_R14_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv523_fc6b_R14_0_I1 /\ ReceiveAckAction => Inv523_fc6b_R14_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv523_fc6b_R14_0_I1,beats
  \* (Inv523_fc6b_R14_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv523_fc6b_R14_0_I1 /\ ReceiveReleaseAction => Inv523_fc6b_R14_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv523_fc6b_R14_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv372_d6ca_R19_1_I1
THEOREM L_21 == TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv372_d6ca_R19_1_I1 /\ Next => Inv372_d6ca_R19_1_I1'
  \* (Inv372_d6ca_R19_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv372_d6ca_R19_1_I1 /\ RequestAction => Inv372_d6ca_R19_1_I1' BY DEF TypeOK,RequestAction,Request,Inv372_d6ca_R19_1_I1
  \* (Inv372_d6ca_R19_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv372_d6ca_R19_1_I1 /\ EnterAction => Inv372_d6ca_R19_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv372_d6ca_R19_1_I1,beats
  \* (Inv372_d6ca_R19_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv372_d6ca_R19_1_I1 /\ ExitAction => Inv372_d6ca_R19_1_I1' BY DEF TypeOK,Inv354_245d_R1_3_I1,ExitAction,Exit,Inv372_d6ca_R19_1_I1,beats,Broadcast
  \* (Inv372_d6ca_R19_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv372_d6ca_R19_1_I1 /\ ReceiveRequestAction => Inv372_d6ca_R19_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv372_d6ca_R19_1_I1
  \* (Inv372_d6ca_R19_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv372_d6ca_R19_1_I1 /\ ReceiveAckAction => Inv372_d6ca_R19_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv372_d6ca_R19_1_I1,beats
  \* (Inv372_d6ca_R19_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv372_d6ca_R19_1_I1 /\ ReceiveReleaseAction => Inv372_d6ca_R19_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv372_d6ca_R19_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv262_72d8_R17_1_I1
THEOREM L_22 == TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv262_72d8_R17_1_I1 /\ Next => Inv262_72d8_R17_1_I1'
  \* (Inv262_72d8_R17_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv262_72d8_R17_1_I1 /\ RequestAction => Inv262_72d8_R17_1_I1' BY DEF TypeOK,RequestAction,Request,Inv262_72d8_R17_1_I1
  \* (Inv262_72d8_R17_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv262_72d8_R17_1_I1 /\ EnterAction => Inv262_72d8_R17_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv262_72d8_R17_1_I1,beats
  \* (Inv262_72d8_R17_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv262_72d8_R17_1_I1 /\ ExitAction => Inv262_72d8_R17_1_I1' BY DEF TypeOK,Inv354_245d_R1_3_I1,ExitAction,Exit,Inv262_72d8_R17_1_I1,beats,Broadcast
  \* (Inv262_72d8_R17_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv262_72d8_R17_1_I1 /\ ReceiveRequestAction => Inv262_72d8_R17_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv262_72d8_R17_1_I1
  \* (Inv262_72d8_R17_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv262_72d8_R17_1_I1 /\ ReceiveAckAction => Inv262_72d8_R17_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv262_72d8_R17_1_I1,beats
  \* (Inv262_72d8_R17_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv262_72d8_R17_1_I1 /\ ReceiveReleaseAction => Inv262_72d8_R17_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv262_72d8_R17_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv362_1b85_R23_0_I2
THEOREM L_23 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv168_a109_R15_0_I1 /\ Inv52_6351_R28_0_I1 /\ Inv362_1b85_R23_0_I2 /\ Next => Inv362_1b85_R23_0_I2'
  \* (Inv362_1b85_R23_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv362_1b85_R23_0_I2 /\ RequestAction => Inv362_1b85_R23_0_I2' BY DEF TypeOK,Inv15_c48d_R4_0_I0,RequestAction,Request,Inv362_1b85_R23_0_I2
  \* (Inv362_1b85_R23_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv362_1b85_R23_0_I2 /\ EnterAction => Inv362_1b85_R23_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv362_1b85_R23_0_I2,beats
  \* (Inv362_1b85_R23_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv362_1b85_R23_0_I2 /\ ExitAction => Inv362_1b85_R23_0_I2' BY DEF TypeOK,ExitAction,Exit,Inv362_1b85_R23_0_I2,beats,Broadcast
  \* (Inv362_1b85_R23_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv168_a109_R15_0_I1 /\ Inv362_1b85_R23_0_I2 /\ ReceiveRequestAction => Inv362_1b85_R23_0_I2' BY DEF TypeOK,Inv168_a109_R15_0_I1,ReceiveRequestAction,ReceiveRequest,Inv362_1b85_R23_0_I2
  \* (Inv362_1b85_R23_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv52_6351_R28_0_I1 /\ Inv362_1b85_R23_0_I2 /\ ReceiveAckAction => Inv362_1b85_R23_0_I2' BY DEF TypeOK,Inv52_6351_R28_0_I1,ReceiveAckAction,ReceiveAck,Inv362_1b85_R23_0_I2,beats
  \* (Inv362_1b85_R23_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv362_1b85_R23_0_I2 /\ ReceiveReleaseAction => Inv362_1b85_R23_0_I2' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv362_1b85_R23_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv52_6351_R28_0_I1
THEOREM L_24 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv883_765c_R11_0_I1 /\ Inv172_849b_R15_0_I1 /\ Inv52_6351_R28_0_I1 /\ Next => Inv52_6351_R28_0_I1'
  \* (Inv52_6351_R28_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv52_6351_R28_0_I1 /\ RequestAction => Inv52_6351_R28_0_I1' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,RequestAction,Request,Inv52_6351_R28_0_I1
  \* (Inv52_6351_R28_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv52_6351_R28_0_I1 /\ EnterAction => Inv52_6351_R28_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv52_6351_R28_0_I1,beats
  \* (Inv52_6351_R28_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv52_6351_R28_0_I1 /\ ExitAction => Inv52_6351_R28_0_I1' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv52_6351_R28_0_I1,beats,Broadcast
  \* (Inv52_6351_R28_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv172_849b_R15_0_I1 /\ Inv52_6351_R28_0_I1 /\ ReceiveRequestAction => Inv52_6351_R28_0_I1' BY DEF TypeOK,Inv172_849b_R15_0_I1,ReceiveRequestAction,ReceiveRequest,Inv52_6351_R28_0_I1
  \* (Inv52_6351_R28_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv52_6351_R28_0_I1 /\ ReceiveAckAction => Inv52_6351_R28_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv52_6351_R28_0_I1,beats
  \* (Inv52_6351_R28_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv52_6351_R28_0_I1 /\ ReceiveReleaseAction => Inv52_6351_R28_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv52_6351_R28_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv3175_ec0b_R23_0_I2
THEOREM L_25 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv883_765c_R11_0_I1 /\ Inv172_849b_R15_0_I1 /\ Inv3175_ec0b_R23_0_I2 /\ Next => Inv3175_ec0b_R23_0_I2'
  \* (Inv3175_ec0b_R23_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv3175_ec0b_R23_0_I2 /\ RequestAction => Inv3175_ec0b_R23_0_I2' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,RequestAction,Request,Inv3175_ec0b_R23_0_I2
  \* (Inv3175_ec0b_R23_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv3175_ec0b_R23_0_I2 /\ EnterAction => Inv3175_ec0b_R23_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv3175_ec0b_R23_0_I2,beats
  \* (Inv3175_ec0b_R23_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv3175_ec0b_R23_0_I2 /\ ExitAction => Inv3175_ec0b_R23_0_I2' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv3175_ec0b_R23_0_I2,beats,Broadcast
  \* (Inv3175_ec0b_R23_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv172_849b_R15_0_I1 /\ Inv3175_ec0b_R23_0_I2 /\ ReceiveRequestAction => Inv3175_ec0b_R23_0_I2' BY DEF TypeOK,Inv172_849b_R15_0_I1,ReceiveRequestAction,ReceiveRequest,Inv3175_ec0b_R23_0_I2
  \* (Inv3175_ec0b_R23_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv3175_ec0b_R23_0_I2 /\ ReceiveAckAction => Inv3175_ec0b_R23_0_I2' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv3175_ec0b_R23_0_I2,beats
  \* (Inv3175_ec0b_R23_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv3175_ec0b_R23_0_I2 /\ ReceiveReleaseAction => Inv3175_ec0b_R23_0_I2' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv3175_ec0b_R23_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1052_a3d0_R2_2_I1
THEOREM L_26 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv790_98d1_R9_1_I1 /\ Inv1052_a3d0_R2_2_I1 /\ Next => Inv1052_a3d0_R2_2_I1'
  \* (Inv1052_a3d0_R2_2_I1,RequestAction)
  <1>1. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv1052_a3d0_R2_2_I1 /\ RequestAction => Inv1052_a3d0_R2_2_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,RequestAction,Request,Inv1052_a3d0_R2_2_I1
  \* (Inv1052_a3d0_R2_2_I1,EnterAction)
  <1>2. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ EnterAction => Inv1052_a3d0_R2_2_I1' BY DEF TypeOK,EnterAction,Enter,Inv1052_a3d0_R2_2_I1,beats
  \* (Inv1052_a3d0_R2_2_I1,ExitAction)
  <1>3. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ ExitAction => Inv1052_a3d0_R2_2_I1' BY DEF TypeOK,ExitAction,Exit,Inv1052_a3d0_R2_2_I1,beats,Broadcast
  \* (Inv1052_a3d0_R2_2_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ ReceiveRequestAction => Inv1052_a3d0_R2_2_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1052_a3d0_R2_2_I1
  \* (Inv1052_a3d0_R2_2_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv790_98d1_R9_1_I1 /\ Inv1052_a3d0_R2_2_I1 /\ ReceiveAckAction => Inv1052_a3d0_R2_2_I1' BY DEF TypeOK,Inv790_98d1_R9_1_I1,ReceiveAckAction,ReceiveAck,Inv1052_a3d0_R2_2_I1,beats
  \* (Inv1052_a3d0_R2_2_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ ReceiveReleaseAction => Inv1052_a3d0_R2_2_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1052_a3d0_R2_2_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv63_dd88_R1_0_I2
THEOREM L_27 == TypeOK /\ Inv10_af7e_R3_1_I0 /\ Inv603_da04_R3_0_I1 /\ Inv63_dd88_R1_0_I2 /\ Next => Inv63_dd88_R1_0_I2'
  \* (Inv63_dd88_R1_0_I2,RequestAction)
  <1>1. TypeOK /\ Inv63_dd88_R1_0_I2 /\ RequestAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,RequestAction,Request,Inv63_dd88_R1_0_I2
  \* (Inv63_dd88_R1_0_I2,EnterAction)
  <1>2. TypeOK /\ Inv63_dd88_R1_0_I2 /\ EnterAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,EnterAction,Enter,Inv63_dd88_R1_0_I2,beats
  \* (Inv63_dd88_R1_0_I2,ExitAction)
  <1>3. TypeOK /\ Inv63_dd88_R1_0_I2 /\ ExitAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,ExitAction,Exit,Inv63_dd88_R1_0_I2,beats,Broadcast
  \* (Inv63_dd88_R1_0_I2,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv10_af7e_R3_1_I0 /\ Inv63_dd88_R1_0_I2 /\ ReceiveRequestAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,Inv10_af7e_R3_1_I0,ReceiveRequestAction,ReceiveRequest,Inv63_dd88_R1_0_I2
  \* (Inv63_dd88_R1_0_I2,ReceiveAckAction)
  <1>5. TypeOK /\ Inv603_da04_R3_0_I1 /\ Inv63_dd88_R1_0_I2 /\ ReceiveAckAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,Inv603_da04_R3_0_I1,ReceiveAckAction,ReceiveAck,Inv63_dd88_R1_0_I2,beats
  \* (Inv63_dd88_R1_0_I2,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv63_dd88_R1_0_I2 /\ ReceiveReleaseAction => Inv63_dd88_R1_0_I2' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv63_dd88_R1_0_I2,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv603_da04_R3_0_I1
THEOREM L_28 == TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv10_af7e_R3_1_I0 /\ Inv603_da04_R3_0_I1 /\ Next => Inv603_da04_R3_0_I1'
  \* (Inv603_da04_R3_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv603_da04_R3_0_I1 /\ RequestAction => Inv603_da04_R3_0_I1' BY DEF TypeOK,RequestAction,Request,Inv603_da04_R3_0_I1
  \* (Inv603_da04_R3_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv603_da04_R3_0_I1 /\ EnterAction => Inv603_da04_R3_0_I1' BY DEF TypeOK,EnterAction,Enter,Inv603_da04_R3_0_I1,beats
  \* (Inv603_da04_R3_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv883_765c_R11_0_I1 /\ Inv603_da04_R3_0_I1 /\ ExitAction => Inv603_da04_R3_0_I1' BY DEF TypeOK,Inv883_765c_R11_0_I1,ExitAction,Exit,Inv603_da04_R3_0_I1,beats,Broadcast
  \* (Inv603_da04_R3_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv10_af7e_R3_1_I0 /\ Inv603_da04_R3_0_I1 /\ ReceiveRequestAction => Inv603_da04_R3_0_I1' BY DEF TypeOK,Inv10_af7e_R3_1_I0,ReceiveRequestAction,ReceiveRequest,Inv603_da04_R3_0_I1
  \* (Inv603_da04_R3_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv603_da04_R3_0_I1 /\ ReceiveAckAction => Inv603_da04_R3_0_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv603_da04_R3_0_I1,beats
  \* (Inv603_da04_R3_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv603_da04_R3_0_I1 /\ ReceiveReleaseAction => Inv603_da04_R3_0_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv603_da04_R3_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv10_af7e_R3_1_I0
THEOREM L_29 == TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv10_af7e_R3_1_I0 /\ Next => Inv10_af7e_R3_1_I0'
  \* (Inv10_af7e_R3_1_I0,RequestAction)
  <1>1. TypeOK /\ Inv10_af7e_R3_1_I0 /\ RequestAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,RequestAction,Request,Inv10_af7e_R3_1_I0
  \* (Inv10_af7e_R3_1_I0,EnterAction)
  <1>2. TypeOK /\ Inv10_af7e_R3_1_I0 /\ EnterAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,EnterAction,Enter,Inv10_af7e_R3_1_I0,beats
  \* (Inv10_af7e_R3_1_I0,ExitAction)
  <1>3. TypeOK /\ Inv354_245d_R1_3_I1 /\ Inv10_af7e_R3_1_I0 /\ ExitAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,Inv354_245d_R1_3_I1,ExitAction,Exit,Inv10_af7e_R3_1_I0,beats,Broadcast
  \* (Inv10_af7e_R3_1_I0,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv10_af7e_R3_1_I0 /\ ReceiveRequestAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv10_af7e_R3_1_I0
  \* (Inv10_af7e_R3_1_I0,ReceiveAckAction)
  <1>5. TypeOK /\ Inv10_af7e_R3_1_I0 /\ ReceiveAckAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv10_af7e_R3_1_I0,beats
  \* (Inv10_af7e_R3_1_I0,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv10_af7e_R3_1_I0 /\ ReceiveReleaseAction => Inv10_af7e_R3_1_I0' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv10_af7e_R3_1_I0,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv5351_fa98_R1_1_I1
THEOREM L_30 == TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv5351_fa98_R1_1_I1 /\ Next => Inv5351_fa98_R1_1_I1'
  \* (Inv5351_fa98_R1_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv5351_fa98_R1_1_I1 /\ RequestAction => Inv5351_fa98_R1_1_I1' BY DEF TypeOK,RequestAction,Request,Inv5351_fa98_R1_1_I1
  \* (Inv5351_fa98_R1_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv15_c48d_R4_0_I0 /\ Inv5351_fa98_R1_1_I1 /\ EnterAction => Inv5351_fa98_R1_1_I1' BY DEF TypeOK,Inv15_c48d_R4_0_I0,EnterAction,Enter,Inv5351_fa98_R1_1_I1,beats
  \* (Inv5351_fa98_R1_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv5351_fa98_R1_1_I1 /\ ExitAction => Inv5351_fa98_R1_1_I1' BY DEF TypeOK,ExitAction,Exit,Inv5351_fa98_R1_1_I1,beats,Broadcast
  \* (Inv5351_fa98_R1_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv5351_fa98_R1_1_I1 /\ ReceiveRequestAction => Inv5351_fa98_R1_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv5351_fa98_R1_1_I1
  \* (Inv5351_fa98_R1_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv5351_fa98_R1_1_I1 /\ ReceiveAckAction => Inv5351_fa98_R1_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv5351_fa98_R1_1_I1,beats
  \* (Inv5351_fa98_R1_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv5351_fa98_R1_1_I1 /\ ReceiveReleaseAction => Inv5351_fa98_R1_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv5351_fa98_R1_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv2428_a275_R1_1_I1
THEOREM L_31 == TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv2428_a275_R1_1_I1 /\ Next => Inv2428_a275_R1_1_I1'
  \* (Inv2428_a275_R1_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_8f4b_R5_0_I1 /\ Inv2428_a275_R1_1_I1 /\ RequestAction => Inv2428_a275_R1_1_I1' BY DEF TypeOK,Inv39_8f4b_R5_0_I1,RequestAction,Request,Inv2428_a275_R1_1_I1
  \* (Inv2428_a275_R1_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv2428_a275_R1_1_I1 /\ EnterAction => Inv2428_a275_R1_1_I1' BY DEF TypeOK,EnterAction,Enter,Inv2428_a275_R1_1_I1,beats
  \* (Inv2428_a275_R1_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv2428_a275_R1_1_I1 /\ ExitAction => Inv2428_a275_R1_1_I1' BY DEF TypeOK,ExitAction,Exit,Inv2428_a275_R1_1_I1,beats,Broadcast
  \* (Inv2428_a275_R1_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv2428_a275_R1_1_I1 /\ ReceiveRequestAction => Inv2428_a275_R1_1_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv2428_a275_R1_1_I1
  \* (Inv2428_a275_R1_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv2428_a275_R1_1_I1 /\ ReceiveAckAction => Inv2428_a275_R1_1_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv2428_a275_R1_1_I1,beats
  \* (Inv2428_a275_R1_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv2428_a275_R1_1_I1 /\ ReceiveReleaseAction => Inv2428_a275_R1_1_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv2428_a275_R1_1_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv686_7d37_R1_2_I1
THEOREM L_32 == TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ Inv686_7d37_R1_2_I1 /\ Next => Inv686_7d37_R1_2_I1'
  \* (Inv686_7d37_R1_2_I1,RequestAction)
  <1>1. TypeOK /\ Inv686_7d37_R1_2_I1 /\ RequestAction => Inv686_7d37_R1_2_I1' BY DEF TypeOK,RequestAction,Request,Inv686_7d37_R1_2_I1
  \* (Inv686_7d37_R1_2_I1,EnterAction)
  <1>2. TypeOK /\ Inv1052_a3d0_R2_2_I1 /\ Inv686_7d37_R1_2_I1 /\ EnterAction => Inv686_7d37_R1_2_I1' BY DEF TypeOK,Inv1052_a3d0_R2_2_I1,EnterAction,Enter,Inv686_7d37_R1_2_I1,beats
  \* (Inv686_7d37_R1_2_I1,ExitAction)
  <1>3. TypeOK /\ Inv686_7d37_R1_2_I1 /\ ExitAction => Inv686_7d37_R1_2_I1' BY DEF TypeOK,ExitAction,Exit,Inv686_7d37_R1_2_I1,beats,Broadcast
  \* (Inv686_7d37_R1_2_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv686_7d37_R1_2_I1 /\ ReceiveRequestAction => Inv686_7d37_R1_2_I1' BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv686_7d37_R1_2_I1
  \* (Inv686_7d37_R1_2_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv686_7d37_R1_2_I1 /\ ReceiveAckAction => Inv686_7d37_R1_2_I1' BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv686_7d37_R1_2_I1,beats
  \* (Inv686_7d37_R1_2_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv686_7d37_R1_2_I1 /\ ReceiveReleaseAction => Inv686_7d37_R1_2_I1' BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv686_7d37_R1_2_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv14778_14cd_R0_0_I2 BY DEF Init, Inv14778_14cd_R0_0_I2, IndGlobal
    <1>3. Init => Inv3023_dc35_R1_0_I2 BY DEF Init, Inv3023_dc35_R1_0_I2, IndGlobal
    <1>4. Init => Inv57_6f6e_R2_0_I1 BY DEF Init, Inv57_6f6e_R2_0_I1, IndGlobal
    <1>5. Init => Inv1106_d0c9_R2_1_I1 BY DEF Init, Inv1106_d0c9_R2_1_I1, IndGlobal
    <1>6. Init => Inv15_c48d_R4_0_I0 BY DEF Init, Inv15_c48d_R4_0_I0, IndGlobal
    <1>7. Init => Inv790_98d1_R9_1_I1 BY DEF Init, Inv790_98d1_R9_1_I1, IndGlobal
    <1>8. Init => Inv883_765c_R11_0_I1 BY DEF Init, Inv883_765c_R11_0_I1, IndGlobal
    <1>9. Init => Inv1067_2e56_R18_0_I1 BY DEF Init, Inv1067_2e56_R18_0_I1, IndGlobal
    <1>10. Init => Inv79_dabf_R20_0_I1 BY DEF Init, Inv79_dabf_R20_0_I1, IndGlobal
    <1>11. Init => Inv2_3687_R21_0_I0 BY DEF Init, Inv2_3687_R21_0_I0, IndGlobal
    <1>12. Init => Inv997_f9fe_R26_0_I1 BY DEF Init, Inv997_f9fe_R26_0_I1, IndGlobal
    <1>13. Init => Inv354_245d_R1_3_I1 BY DEF Init, Inv354_245d_R1_3_I1, IndGlobal
    <1>14. Init => Inv637_2954_R7_0_I1 BY DEF Init, Inv637_2954_R7_0_I1, IndGlobal
    <1>15. Init => Inv168_a109_R15_0_I1 BY DEF Init, Inv168_a109_R15_0_I1, IndGlobal
    <1>16. Init => Inv172_849b_R15_0_I1 BY DEF Init, Inv172_849b_R15_0_I1, IndGlobal
    <1>17. Init => Inv1036_6109_R21_1_I1 BY DEF Init, Inv1036_6109_R21_1_I1, IndGlobal
    <1>18. Init => Inv2204_12c5_R7_1_I1 BY DEF Init, Inv2204_12c5_R7_1_I1, IndGlobal
    <1>19. Init => Inv39_8f4b_R5_0_I1 BY DEF Init, Inv39_8f4b_R5_0_I1, IndGlobal
    <1>20. Init => Inv523_fc6b_R14_0_I1 BY DEF Init, Inv523_fc6b_R14_0_I1, IndGlobal
    <1>21. Init => Inv372_d6ca_R19_1_I1 BY DEF Init, Inv372_d6ca_R19_1_I1, IndGlobal
    <1>22. Init => Inv262_72d8_R17_1_I1 BY DEF Init, Inv262_72d8_R17_1_I1, IndGlobal
    <1>23. Init => Inv362_1b85_R23_0_I2 BY DEF Init, Inv362_1b85_R23_0_I2, IndGlobal
    <1>24. Init => Inv52_6351_R28_0_I1 BY DEF Init, Inv52_6351_R28_0_I1, IndGlobal
    <1>25. Init => Inv3175_ec0b_R23_0_I2 BY DEF Init, Inv3175_ec0b_R23_0_I2, IndGlobal
    <1>26. Init => Inv1052_a3d0_R2_2_I1 BY DEF Init, Inv1052_a3d0_R2_2_I1, IndGlobal
    <1>27. Init => Inv63_dd88_R1_0_I2 BY DEF Init, Inv63_dd88_R1_0_I2, IndGlobal
    <1>28. Init => Inv603_da04_R3_0_I1 BY DEF Init, Inv603_da04_R3_0_I1, IndGlobal
    <1>29. Init => Inv10_af7e_R3_1_I0 BY DEF Init, Inv10_af7e_R3_1_I0, IndGlobal
    <1>30. Init => Inv5351_fa98_R1_1_I1 BY DEF Init, Inv5351_fa98_R1_1_I1, IndGlobal
    <1>31. Init => Inv2428_a275_R1_1_I1 BY DEF Init, Inv2428_a275_R1_1_I1, IndGlobal
    <1>32. Init => Inv686_7d37_R1_2_I1 BY DEF Init, Inv686_7d37_R1_2_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32 DEF Next, IndGlobal

====