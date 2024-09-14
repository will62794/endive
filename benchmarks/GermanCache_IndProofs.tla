------------------------- MODULE GermanCache_IndProofs -------------------------
EXTENDS GermanCache


USE DEF CtrlProp1
USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE


\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 46
\* num proof obligations: 552
Safety == CtrlProp1
Inv122_03a2_R0_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Cache[VARJ].State = "I") \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv10_3662_R0_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(Chan2[VARJ].Cmd = "GntS"))
Inv5427_0d22_R1_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "GntE") \/ (~(VARI # VARJ)))
Inv32_1336_R1_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(Chan2[VARJ].Cmd = "GntS"))
Inv22_d756_R1_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((ShrSet[VARI]))
Inv12_513a_R2_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Cache[VARI].State = "E"))
Inv1_85ad_R3_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
Inv5_a2c7_R3_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv6423_fc2f_R3_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))
Inv11_e00a_R5_0_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv12_4ccb_R5_1_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "GntS"))
Inv10_8267_R5_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((Chan3[VARI].Cmd = "Empty"))
Inv7_7199_R6_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Cache[VARJ].State = "E"))
Inv1_eb94_R7_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((Chan3[VARI].Cmd = "Empty"))
Inv104_0f39_R7_1_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(InvSet[VARI]))
Inv15_5b11_R8_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "GntE"))
Inv9619_4ca8_R9_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARJ].Cmd = "GntE") \/ (~(VARI # VARJ)) \/ (~(ShrSet[VARI]))
Inv11_c03f_R12_0_I1 == \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Empty") \/ ((Chan3[VARJ].Cmd = "Empty"))
Inv8923_9eca_R13_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(Chan2[VARJ].Cmd = "Inv") \/ (~(VARI # VARJ)))
Inv14_9e93_R14_0_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
Inv2748_0201_R14_1_I2 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((CurCmd = "ReqE")) \/ ((ExGntd))
Inv13_45c1_R14_2_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(InvSet[VARI]))
Inv26_259c_R15_0_I1 == \A VARJ \in NODE : (Chan3[VARJ].Cmd = "Empty") \/ (~(InvSet[VARJ]))
Inv64_c47d_R16_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(Chan2[VARJ].Cmd = "Inv"))
Inv3306_6920_R19_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))
Inv39_7204_R20_0_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv1036_a1d6_R21_0_I3 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd)) \/ ((Chan3[VARJ].Cmd = "Empty")) \/ (~(VARI # VARJ))
Inv1611_1275_R21_1_I2 == \A VARI \in NODE : (CurCmd = "ReqE") \/ ((ExGntd) \/ (~(Chan2[VARI].Cmd = "Inv")))
Inv3716_575b_R22_0_I2 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((CurCmd = "ReqE") \/ ((CurCmd = "ReqS")))
Inv76_d564_R22_2_I1 == \A VARI \in NODE : ~(Chan2[VARI].Cmd = "Inv") \/ (~(InvSet[VARI]))
Inv6436_bea9_R25_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(ShrSet[VARJ])) \/ (~(VARI # VARJ))
Inv20_5035_R26_0_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv13_812b_R27_1_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((Chan3[VARI].Cmd = "InvAck"))
Inv50_ba79_R27_1_I1 == \A VARI \in NODE : ~(Cache[VARI].State = "S") \/ (~(ExGntd))
Inv45_2bf0_R27_1_I1 == \A VARI \in NODE : ~(Cache[VARI].State = "I") \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv3857_1b30_R28_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "Inv") \/ (~(ExGntd)))
Inv651_b778_R29_2_I2 == \A VARI \in NODE : (CurCmd = "ReqE") \/ ((CurCmd = "ReqS")) \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv43_39a8_R34_0_I1 == \A VARI \in NODE : ~(Chan2[VARI].Cmd = "GntS") \/ (~(ExGntd))
Inv1511_683a_R35_0_I2 == \A VARI \in NODE : ~(Cache[VARI].State = "I") \/ (~(Chan2[VARI].Cmd = "Empty")) \/ (~(InvSet[VARI]))
Inv28_f7af_R36_1_I2 == \A VARJ \in NODE : (Cache[VARJ].State = "E") \/ (~(Chan2[VARJ].Cmd = "Inv")) \/ (~(ExGntd))
Inv1067_2e74_R36_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARJ].Cmd = "Empty") \/ (~(ExGntd) \/ (~(InvSet[VARI])))
Inv2445_d313_R39_0_I4 == \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Inv") \/ ((CurCmd = "ReqE") \/ ((CurCmd = "ReqS") \/ (~(Cache[VARJ].State = "I") \/ (~(ShrSet[VARJ])))) \/ (~(Chan2[VARJ].Cmd = "Empty")))
Inv100_1def_R41_3_I1 == \A VARJ \in NODE : ~(Chan2[VARJ].Cmd = "Inv") \/ (~(InvSet[VARJ]))
Inv654_d73e_R42_0_I4 == \A VARI \in NODE : \A VARJ \in NODE : (Cache[VARI].State = "S") \/ (~(Cache[VARJ].State = "I")) \/ ((ExGntd)) \/ (~(CurCmd = "ReqS")) \/ (~(ShrSet[VARI])) \/ (~(Chan2[VARI].Cmd = "Empty"))
Inv2246_d6a1_R44_1_I3 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd) \/ (~(ShrSet[VARJ])) \/ (~(VARI # VARJ)))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv122_03a2_R0_0_I1
  /\ Inv5427_0d22_R1_0_I2
  /\ Inv1_85ad_R3_0_I1
  /\ Inv1_eb94_R7_0_I1
  /\ Inv14_9e93_R14_0_I1
  /\ Inv39_7204_R20_0_I1
  /\ Inv20_5035_R26_0_I1
  /\ Inv13_45c1_R14_2_I1
  /\ Inv3716_575b_R22_0_I2
  /\ Inv2748_0201_R14_1_I2
  /\ Inv1036_a1d6_R21_0_I3
  /\ Inv11_c03f_R12_0_I1
  /\ Inv13_812b_R27_1_I1
  /\ Inv50_ba79_R27_1_I1
  /\ Inv43_39a8_R34_0_I1
  /\ Inv22_d756_R1_2_I1
  /\ Inv11_e00a_R5_0_I1
  /\ Inv12_4ccb_R5_1_I1
  /\ Inv10_8267_R5_2_I1
  /\ Inv7_7199_R6_1_I1
  /\ Inv15_5b11_R8_0_I1
  /\ Inv64_c47d_R16_1_I1
  /\ Inv6423_fc2f_R3_2_I2
  /\ Inv9619_4ca8_R9_0_I2
  /\ Inv5_a2c7_R3_1_I1
  /\ Inv104_0f39_R7_1_I1
  /\ Inv26_259c_R15_0_I1
  /\ Inv76_d564_R22_2_I1
  /\ Inv651_b778_R29_2_I2
  /\ Inv1611_1275_R21_1_I2
  /\ Inv3857_1b30_R28_0_I2
  /\ Inv28_f7af_R36_1_I2
  /\ Inv1511_683a_R35_0_I2
  /\ Inv2445_d313_R39_0_I4
  /\ Inv654_d73e_R42_0_I4
  /\ Inv2246_d6a1_R44_1_I3
  /\ Inv6436_bea9_R25_1_I2
  /\ Inv12_513a_R2_1_I1
  /\ Inv8923_9eca_R13_1_I2
  /\ Inv3306_6920_R19_1_I2
  /\ Inv1067_2e74_R36_2_I2
  /\ Inv100_1def_R41_3_I1
  /\ Inv45_2bf0_R27_1_I1
  /\ Inv32_1336_R1_1_I1
  /\ Inv10_3662_R0_1_I1


\* mean in-degree: 2.391304347826087
\* median in-degree: 2
\* max in-degree: 7
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == \E N \in Nat : NODE = 1..N /\ IsFiniteSet(NODE) /\ NODE # {}
ASSUME A1 == \E N \in Nat : DATA = 1..N /\ IsFiniteSet(DATA) /\ DATA # {}

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1
  \* (TypeOK,SendReqEAction)
  <1>1. TypeOK /\ TypeOK /\ SendReqEAction => TypeOK' BY DEF TypeOK,SendReqEAction,SendReqE,TypeOK
  \* (TypeOK,RecvReqSAction)
  <1>2. TypeOK /\ TypeOK /\ RecvReqSAction => TypeOK' BY DEF TypeOK,RecvReqSAction,RecvReqS,TypeOK
  \* (TypeOK,RecvReqEAction)
  <1>3. TypeOK /\ TypeOK /\ RecvReqEAction => TypeOK' BY DEF TypeOK,RecvReqEAction,RecvReqE,TypeOK
  \* (TypeOK,SendInvAction)
  <1>4. TypeOK /\ TypeOK /\ SendInvAction => TypeOK' BY DEF TypeOK,SendInvAction,SendInv,TypeOK
  \* (TypeOK,SendInvAckAction)
  <1>5. TypeOK /\ TypeOK /\ SendInvAckAction => TypeOK' BY DEF TypeOK,SendInvAckAction,SendInvAck,TypeOK
  \* (TypeOK,RecvInvAckAction)
  <1>6. TypeOK /\ TypeOK /\ RecvInvAckAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RecvInvAckAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (Cache \in [NODE -> CACHE])'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>2. (Chan1 \in [NODE -> MSG])'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>3. (Chan2 \in [NODE -> MSG])'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>4. (Chan3 \in [NODE -> MSG])'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>5. (InvSet \in [NODE -> BOOLEAN])'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>6. (ShrSet \in [NODE -> BOOLEAN])'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>7. (ExGntd \in BOOLEAN)'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>8. (CurCmd \in MSG_CMD)'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>9. (CurPtr \in NODE)'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>10. (MemData \in DATA)'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>11. (AuxData \in DATA)'
      BY DEF TypeOK,RecvInvAckAction,RecvInvAck,TypeOK
    <2>12. QED
      BY <2>1, <2>10, <2>11, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,SendGntSAction)
  <1>7. TypeOK /\ TypeOK /\ SendGntSAction => TypeOK' BY DEF TypeOK,SendGntSAction,SendGntS,TypeOK
  \* (TypeOK,SendGntEAction)
  <1>8. TypeOK /\ TypeOK /\ SendGntEAction => TypeOK' BY DEF TypeOK,SendGntEAction,SendGntE,TypeOK
  \* (TypeOK,RecvGntSAction)
  <1>9. TypeOK /\ TypeOK /\ RecvGntSAction => TypeOK' BY DEF TypeOK,RecvGntSAction,RecvGntS,TypeOK
  \* (TypeOK,RecvGntEAction)
  <1>10. TypeOK /\ TypeOK /\ RecvGntEAction => TypeOK' BY DEF TypeOK,RecvGntEAction,RecvGntE,TypeOK
  \* (TypeOK,StoreAction)
  <1>11. TypeOK /\ TypeOK /\ StoreAction => TypeOK' BY DEF TypeOK,StoreAction,Store,TypeOK
  \* (TypeOK,SendReqSAction)
  <1>12. TypeOK /\ TypeOK /\ SendReqSAction => TypeOK' BY DEF TypeOK,SendReqSAction,SendReqS,TypeOK
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv10_3662_R0_1_I1 /\ Inv122_03a2_R0_0_I1 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1
  \* (Safety,SendReqEAction)
  <1>1. TypeOK /\ Safety /\ SendReqEAction => Safety' BY DEF TypeOK,SendReqEAction,SendReqE,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,RecvReqSAction)
  <1>2. TypeOK /\ Safety /\ RecvReqSAction => Safety' BY DEF TypeOK,RecvReqSAction,RecvReqS,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,RecvReqEAction)
  <1>3. TypeOK /\ Safety /\ RecvReqEAction => Safety' BY DEF TypeOK,RecvReqEAction,RecvReqE,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,SendInvAction)
  <1>4. TypeOK /\ Safety /\ SendInvAction => Safety' BY DEF TypeOK,SendInvAction,SendInv,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,SendInvAckAction)
  <1>5. TypeOK /\ Safety /\ SendInvAckAction => Safety' BY DEF TypeOK,SendInvAckAction,SendInvAck,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,RecvInvAckAction)
  <1>6. TypeOK /\ Safety /\ RecvInvAckAction => Safety' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,SendGntSAction)
  <1>7. TypeOK /\ Safety /\ SendGntSAction => Safety' BY DEF TypeOK,SendGntSAction,SendGntS,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,SendGntEAction)
  <1>8. TypeOK /\ Safety /\ SendGntEAction => Safety' BY DEF TypeOK,SendGntEAction,SendGntE,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,RecvGntSAction)
  <1>9. TypeOK /\ Inv10_3662_R0_1_I1 /\ Safety /\ RecvGntSAction => Safety' BY DEF TypeOK,Inv10_3662_R0_1_I1,RecvGntSAction,RecvGntS,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,RecvGntEAction)
  <1>10. TypeOK /\ Inv122_03a2_R0_0_I1 /\ Safety /\ RecvGntEAction => Safety' BY DEF TypeOK,Inv122_03a2_R0_0_I1,RecvGntEAction,RecvGntE,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,StoreAction)
  <1>11. TypeOK /\ Safety /\ StoreAction => Safety' BY DEF TypeOK,StoreAction,Store,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,SendReqSAction)
  <1>12. TypeOK /\ Safety /\ SendReqSAction => Safety' BY DEF TypeOK,SendReqSAction,SendReqS,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv122_03a2_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv22_d756_R1_2_I1 /\ Inv32_1336_R1_1_I1 /\ Inv5427_0d22_R1_0_I2 /\ Inv122_03a2_R0_0_I1 /\ Next => Inv122_03a2_R0_0_I1'
  <1>. USE A0,A1
  \* (Inv122_03a2_R0_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv122_03a2_R0_0_I1 /\ SendReqEAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv122_03a2_R0_0_I1 /\ RecvReqSAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv122_03a2_R0_0_I1 /\ RecvReqEAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv122_03a2_R0_0_I1 /\ SendInvAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv122_03a2_R0_0_I1 /\ SendInvAckAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv122_03a2_R0_0_I1 /\ RecvInvAckAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv122_03a2_R0_0_I1 /\ SendGntSAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv22_d756_R1_2_I1 /\ Inv122_03a2_R0_0_I1 /\ SendGntEAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,Inv22_d756_R1_2_I1,SendGntEAction,SendGntE,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv32_1336_R1_1_I1 /\ Inv122_03a2_R0_0_I1 /\ RecvGntSAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,Inv32_1336_R1_1_I1,RecvGntSAction,RecvGntS,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ Inv122_03a2_R0_0_I1 /\ RecvGntEAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,Inv5427_0d22_R1_0_I2,RecvGntEAction,RecvGntE,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv122_03a2_R0_0_I1 /\ StoreAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,StoreAction,Store,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv122_03a2_R0_0_I1 /\ SendReqSAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv122_03a2_R0_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5427_0d22_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ Inv5_a2c7_R3_1_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv5427_0d22_R1_0_I2 /\ Next => Inv5427_0d22_R1_0_I2'
  <1>. USE A0,A1
  \* (Inv5427_0d22_R1_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ SendReqEAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ RecvReqSAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ RecvReqEAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ Inv5427_0d22_R1_0_I2 /\ SendInvAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,Inv6423_fc2f_R3_2_I2,SendInvAction,SendInv,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ SendInvAckAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ RecvInvAckAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv5427_0d22_R1_0_I2 /\ SendGntSAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv5427_0d22_R1_0_I2 /\ SendGntEAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ RecvGntSAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ RecvGntEAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ StoreAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,StoreAction,Store,Inv5427_0d22_R1_0_I2
  \* (Inv5427_0d22_R1_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv5427_0d22_R1_0_I2 /\ SendReqSAction => Inv5427_0d22_R1_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv5427_0d22_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_85ad_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv104_0f39_R7_1_I1 /\ Inv1_eb94_R7_0_I1 /\ Inv1_85ad_R3_0_I1 /\ Next => Inv1_85ad_R3_0_I1'
  <1>. USE A0,A1
  \* (Inv1_85ad_R3_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendReqEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvReqSAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvReqEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv104_0f39_R7_1_I1 /\ Inv1_85ad_R3_0_I1 /\ SendInvAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,Inv104_0f39_R7_1_I1,SendInvAction,SendInv,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendInvAckAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1_eb94_R7_0_I1 /\ Inv1_85ad_R3_0_I1 /\ RecvInvAckAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,Inv1_eb94_R7_0_I1,RecvInvAckAction,RecvInvAck,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendGntSAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendGntEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvGntSAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvGntEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv1_85ad_R3_0_I1 /\ StoreAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,StoreAction,Store,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendReqSAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1_85ad_R3_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_eb94_R7_0_I1
THEOREM L_5 == TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv2748_0201_R14_1_I2 /\ Inv14_9e93_R14_0_I1 /\ Inv1_eb94_R7_0_I1 /\ Next => Inv1_eb94_R7_0_I1'
  <1>. USE A0,A1
  \* (Inv1_eb94_R7_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendReqEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvReqSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvReqEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv1_eb94_R7_0_I1 /\ SendInvAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv13_45c1_R14_2_I1,SendInvAction,SendInv,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendInvAckAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvInvAckAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv2748_0201_R14_1_I2 /\ Inv1_eb94_R7_0_I1 /\ SendGntSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv2748_0201_R14_1_I2,SendGntSAction,SendGntS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ Inv1_eb94_R7_0_I1 /\ SendGntEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv14_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvGntSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvGntEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv1_eb94_R7_0_I1 /\ StoreAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,StoreAction,Store,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendReqSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1_eb94_R7_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv14_9e93_R14_0_I1
THEOREM L_6 == TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv14_9e93_R14_0_I1 /\ Next => Inv14_9e93_R14_0_I1'
  <1>. USE A0,A1
  \* (Inv14_9e93_R14_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv14_9e93_R14_0_I1 /\ SendReqEAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv14_9e93_R14_0_I1 /\ RecvReqSAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv14_9e93_R14_0_I1 /\ RecvReqEAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv14_9e93_R14_0_I1 /\ SendInvAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv14_9e93_R14_0_I1 /\ SendInvAckAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendInvAckAction,SendInvAck,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv14_9e93_R14_0_I1 /\ RecvInvAckAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv14_9e93_R14_0_I1 /\ SendGntSAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ SendGntEAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv14_9e93_R14_0_I1 /\ RecvGntSAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv14_9e93_R14_0_I1 /\ RecvGntEAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv14_9e93_R14_0_I1 /\ StoreAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,StoreAction,Store,Inv14_9e93_R14_0_I1
  \* (Inv14_9e93_R14_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv14_9e93_R14_0_I1 /\ SendReqSAction => Inv14_9e93_R14_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv14_9e93_R14_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv39_7204_R20_0_I1
THEOREM L_7 == TypeOK /\ Inv104_0f39_R7_1_I1 /\ Inv20_5035_R26_0_I1 /\ Inv39_7204_R20_0_I1 /\ Next => Inv39_7204_R20_0_I1'
  <1>. USE A0,A1
  \* (Inv39_7204_R20_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv39_7204_R20_0_I1 /\ SendReqEAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv39_7204_R20_0_I1 /\ RecvReqSAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv39_7204_R20_0_I1 /\ RecvReqEAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv104_0f39_R7_1_I1 /\ Inv39_7204_R20_0_I1 /\ SendInvAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,Inv104_0f39_R7_1_I1,SendInvAction,SendInv,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv39_7204_R20_0_I1 /\ SendInvAckAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv20_5035_R26_0_I1 /\ Inv39_7204_R20_0_I1 /\ RecvInvAckAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,Inv20_5035_R26_0_I1,RecvInvAckAction,RecvInvAck,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv39_7204_R20_0_I1 /\ SendGntSAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ SendGntEAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv39_7204_R20_0_I1 /\ RecvGntSAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv39_7204_R20_0_I1 /\ RecvGntEAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv39_7204_R20_0_I1 /\ StoreAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,StoreAction,Store,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv39_7204_R20_0_I1 /\ SendReqSAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv39_7204_R20_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv20_5035_R26_0_I1
THEOREM L_8 == TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv20_5035_R26_0_I1 /\ Next => Inv20_5035_R26_0_I1'
  <1>. USE A0,A1
  \* (Inv20_5035_R26_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv20_5035_R26_0_I1 /\ SendReqEAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv20_5035_R26_0_I1 /\ RecvReqSAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv20_5035_R26_0_I1 /\ RecvReqEAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv20_5035_R26_0_I1 /\ SendInvAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,Inv13_45c1_R14_2_I1,SendInvAction,SendInv,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv20_5035_R26_0_I1 /\ SendInvAckAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv20_5035_R26_0_I1 /\ RecvInvAckAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv20_5035_R26_0_I1 /\ SendGntSAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv20_5035_R26_0_I1 /\ SendGntEAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv20_5035_R26_0_I1 /\ RecvGntSAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv20_5035_R26_0_I1 /\ RecvGntEAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv20_5035_R26_0_I1 /\ StoreAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,StoreAction,Store,Inv20_5035_R26_0_I1
  \* (Inv20_5035_R26_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv20_5035_R26_0_I1 /\ SendReqSAction => Inv20_5035_R26_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv20_5035_R26_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv13_45c1_R14_2_I1
THEOREM L_9 == TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv3716_575b_R22_0_I2 /\ Inv76_d564_R22_2_I1 /\ Inv13_45c1_R14_2_I1 /\ Next => Inv13_45c1_R14_2_I1'
  <1>. USE A0,A1
  \* (Inv13_45c1_R14_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv13_45c1_R14_2_I1 /\ SendReqEAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv13_45c1_R14_2_I1 /\ RecvReqSAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,Inv3716_575b_R22_0_I2,RecvReqSAction,RecvReqS,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv13_45c1_R14_2_I1 /\ RecvReqEAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,Inv3716_575b_R22_0_I2,RecvReqEAction,RecvReqE,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_45c1_R14_2_I1 /\ SendInvAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv76_d564_R22_2_I1 /\ Inv13_45c1_R14_2_I1 /\ SendInvAckAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,Inv76_d564_R22_2_I1,SendInvAckAction,SendInvAck,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv13_45c1_R14_2_I1 /\ RecvInvAckAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv13_45c1_R14_2_I1 /\ SendGntSAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv13_45c1_R14_2_I1 /\ SendGntEAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv13_45c1_R14_2_I1 /\ RecvGntSAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv13_45c1_R14_2_I1 /\ RecvGntEAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv13_45c1_R14_2_I1 /\ StoreAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,StoreAction,Store,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv13_45c1_R14_2_I1 /\ SendReqSAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv13_45c1_R14_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3716_575b_R22_0_I2
THEOREM L_10 == TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv2748_0201_R14_1_I2 /\ Inv14_9e93_R14_0_I1 /\ Inv3716_575b_R22_0_I2 /\ Next => Inv3716_575b_R22_0_I2'
  <1>. USE A0,A1
  \* (Inv3716_575b_R22_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv3716_575b_R22_0_I2 /\ SendReqEAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv3716_575b_R22_0_I2 /\ RecvReqSAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv3716_575b_R22_0_I2 /\ RecvReqEAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv3716_575b_R22_0_I2 /\ SendInvAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv3716_575b_R22_0_I2 /\ SendInvAckAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,Inv651_b778_R29_2_I2,SendInvAckAction,SendInvAck,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3716_575b_R22_0_I2 /\ RecvInvAckAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2748_0201_R14_1_I2 /\ Inv3716_575b_R22_0_I2 /\ SendGntSAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,Inv2748_0201_R14_1_I2,SendGntSAction,SendGntS,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ Inv3716_575b_R22_0_I2 /\ SendGntEAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,Inv14_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv3716_575b_R22_0_I2 /\ RecvGntSAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv3716_575b_R22_0_I2 /\ RecvGntEAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv3716_575b_R22_0_I2 /\ StoreAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,StoreAction,Store,Inv3716_575b_R22_0_I2
  \* (Inv3716_575b_R22_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv3716_575b_R22_0_I2 /\ SendReqSAction => Inv3716_575b_R22_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3716_575b_R22_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2748_0201_R14_1_I2
THEOREM L_11 == TypeOK /\ Inv1611_1275_R21_1_I2 /\ Inv1036_a1d6_R21_0_I3 /\ Inv2748_0201_R14_1_I2 /\ Next => Inv2748_0201_R14_1_I2'
  <1>. USE A0,A1
  \* (Inv2748_0201_R14_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2748_0201_R14_1_I2 /\ SendReqEAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2748_0201_R14_1_I2 /\ RecvReqSAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2748_0201_R14_1_I2 /\ RecvReqEAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2748_0201_R14_1_I2 /\ SendInvAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1611_1275_R21_1_I2 /\ Inv2748_0201_R14_1_I2 /\ SendInvAckAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,Inv1611_1275_R21_1_I2,SendInvAckAction,SendInvAck,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ Inv2748_0201_R14_1_I2 /\ RecvInvAckAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,Inv1036_a1d6_R21_0_I3,RecvInvAckAction,RecvInvAck,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2748_0201_R14_1_I2 /\ SendGntSAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv2748_0201_R14_1_I2 /\ SendGntEAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2748_0201_R14_1_I2 /\ RecvGntSAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv2748_0201_R14_1_I2 /\ RecvGntEAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv2748_0201_R14_1_I2 /\ StoreAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,StoreAction,Store,Inv2748_0201_R14_1_I2
  \* (Inv2748_0201_R14_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2748_0201_R14_1_I2 /\ SendReqSAction => Inv2748_0201_R14_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2748_0201_R14_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1036_a1d6_R21_0_I3
THEOREM L_12 == TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv13_812b_R27_1_I1 /\ Inv50_ba79_R27_1_I1 /\ Inv7_7199_R6_1_I1 /\ Inv45_2bf0_R27_1_I1 /\ Inv14_9e93_R14_0_I1 /\ Inv1036_a1d6_R21_0_I3 /\ Next => Inv1036_a1d6_R21_0_I3'
  <1>. USE A0,A1
  \* (Inv1036_a1d6_R21_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ SendReqEAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ RecvReqSAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ RecvReqEAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ SendInvAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv13_812b_R27_1_I1 /\ Inv50_ba79_R27_1_I1 /\ Inv7_7199_R6_1_I1 /\ Inv45_2bf0_R27_1_I1 /\ Inv1036_a1d6_R21_0_I3 /\ SendInvAckAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,Inv11_c03f_R12_0_I1,Inv13_812b_R27_1_I1,Inv50_ba79_R27_1_I1,Inv7_7199_R6_1_I1,Inv45_2bf0_R27_1_I1,SendInvAckAction,SendInvAck,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ RecvInvAckAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ SendGntSAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ Inv1036_a1d6_R21_0_I3 /\ SendGntEAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,Inv14_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ RecvGntSAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ RecvGntEAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ StoreAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,StoreAction,Store,Inv1036_a1d6_R21_0_I3
  \* (Inv1036_a1d6_R21_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv1036_a1d6_R21_0_I3 /\ SendReqSAction => Inv1036_a1d6_R21_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1036_a1d6_R21_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_c03f_R12_0_I1
THEOREM L_13 == TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv2748_0201_R14_1_I2 /\ Inv14_9e93_R14_0_I1 /\ Inv11_c03f_R12_0_I1 /\ Next => Inv11_c03f_R12_0_I1'
  <1>. USE A0,A1
  \* (Inv11_c03f_R12_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv11_c03f_R12_0_I1 /\ SendReqEAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv11_c03f_R12_0_I1 /\ RecvReqSAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv11_c03f_R12_0_I1 /\ RecvReqEAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv11_c03f_R12_0_I1 /\ SendInvAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,Inv13_45c1_R14_2_I1,SendInvAction,SendInv,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_c03f_R12_0_I1 /\ SendInvAckAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv11_c03f_R12_0_I1 /\ RecvInvAckAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv2748_0201_R14_1_I2 /\ Inv11_c03f_R12_0_I1 /\ SendGntSAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,Inv2748_0201_R14_1_I2,SendGntSAction,SendGntS,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ Inv11_c03f_R12_0_I1 /\ SendGntEAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,Inv14_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_c03f_R12_0_I1 /\ RecvGntSAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv11_c03f_R12_0_I1 /\ RecvGntEAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv11_c03f_R12_0_I1 /\ StoreAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,StoreAction,Store,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv11_c03f_R12_0_I1 /\ SendReqSAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv11_c03f_R12_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv13_812b_R27_1_I1
THEOREM L_14 == TypeOK /\ Inv13_812b_R27_1_I1 /\ Next => Inv13_812b_R27_1_I1'
  <1>. USE A0,A1
  \* (Inv13_812b_R27_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv13_812b_R27_1_I1 /\ SendReqEAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv13_812b_R27_1_I1 /\ RecvReqSAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv13_812b_R27_1_I1 /\ RecvReqEAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_812b_R27_1_I1 /\ SendInvAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv13_812b_R27_1_I1 /\ SendInvAckAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv13_812b_R27_1_I1 /\ RecvInvAckAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv13_812b_R27_1_I1 /\ SendGntSAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv13_812b_R27_1_I1 /\ SendGntEAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv13_812b_R27_1_I1 /\ RecvGntSAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv13_812b_R27_1_I1 /\ RecvGntEAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv13_812b_R27_1_I1 /\ StoreAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,StoreAction,Store,Inv13_812b_R27_1_I1
  \* (Inv13_812b_R27_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv13_812b_R27_1_I1 /\ SendReqSAction => Inv13_812b_R27_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv13_812b_R27_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv50_ba79_R27_1_I1
THEOREM L_15 == TypeOK /\ Inv22_d756_R1_2_I1 /\ Inv43_39a8_R34_0_I1 /\ Inv50_ba79_R27_1_I1 /\ Next => Inv50_ba79_R27_1_I1'
  <1>. USE A0,A1
  \* (Inv50_ba79_R27_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv50_ba79_R27_1_I1 /\ SendReqEAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv50_ba79_R27_1_I1 /\ RecvReqSAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv50_ba79_R27_1_I1 /\ RecvReqEAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv50_ba79_R27_1_I1 /\ SendInvAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv50_ba79_R27_1_I1 /\ SendInvAckAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv50_ba79_R27_1_I1 /\ RecvInvAckAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv50_ba79_R27_1_I1 /\ SendGntSAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv22_d756_R1_2_I1 /\ Inv50_ba79_R27_1_I1 /\ SendGntEAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,Inv22_d756_R1_2_I1,SendGntEAction,SendGntE,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv43_39a8_R34_0_I1 /\ Inv50_ba79_R27_1_I1 /\ RecvGntSAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,Inv43_39a8_R34_0_I1,RecvGntSAction,RecvGntS,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv50_ba79_R27_1_I1 /\ RecvGntEAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv50_ba79_R27_1_I1 /\ StoreAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,StoreAction,Store,Inv50_ba79_R27_1_I1
  \* (Inv50_ba79_R27_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv50_ba79_R27_1_I1 /\ SendReqSAction => Inv50_ba79_R27_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv50_ba79_R27_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv43_39a8_R34_0_I1
THEOREM L_16 == TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv43_39a8_R34_0_I1 /\ Next => Inv43_39a8_R34_0_I1'
  <1>. USE A0,A1
  \* (Inv43_39a8_R34_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv43_39a8_R34_0_I1 /\ SendReqEAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv43_39a8_R34_0_I1 /\ RecvReqSAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv43_39a8_R34_0_I1 /\ RecvReqEAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv43_39a8_R34_0_I1 /\ SendInvAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv43_39a8_R34_0_I1 /\ SendInvAckAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv43_39a8_R34_0_I1 /\ RecvInvAckAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv43_39a8_R34_0_I1 /\ SendGntSAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv43_39a8_R34_0_I1 /\ SendGntEAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv43_39a8_R34_0_I1 /\ RecvGntSAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv43_39a8_R34_0_I1 /\ RecvGntEAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv43_39a8_R34_0_I1 /\ StoreAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,StoreAction,Store,Inv43_39a8_R34_0_I1
  \* (Inv43_39a8_R34_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv43_39a8_R34_0_I1 /\ SendReqSAction => Inv43_39a8_R34_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv43_39a8_R34_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv22_d756_R1_2_I1
THEOREM L_17 == TypeOK /\ Inv10_8267_R5_2_I1 /\ Inv12_4ccb_R5_1_I1 /\ Inv11_e00a_R5_0_I1 /\ Inv22_d756_R1_2_I1 /\ Next => Inv22_d756_R1_2_I1'
  <1>. USE A0,A1
  \* (Inv22_d756_R1_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv22_d756_R1_2_I1 /\ SendReqEAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv22_d756_R1_2_I1 /\ RecvReqSAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv22_d756_R1_2_I1 /\ RecvReqEAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv22_d756_R1_2_I1 /\ SendInvAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv22_d756_R1_2_I1 /\ SendInvAckAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_8267_R5_2_I1 /\ Inv22_d756_R1_2_I1 /\ RecvInvAckAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,Inv10_8267_R5_2_I1,RecvInvAckAction,RecvInvAck,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv22_d756_R1_2_I1 /\ SendGntSAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv22_d756_R1_2_I1 /\ SendGntEAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ Inv22_d756_R1_2_I1 /\ RecvGntSAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,Inv12_4ccb_R5_1_I1,RecvGntSAction,RecvGntS,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv11_e00a_R5_0_I1 /\ Inv22_d756_R1_2_I1 /\ RecvGntEAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,Inv11_e00a_R5_0_I1,RecvGntEAction,RecvGntE,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv22_d756_R1_2_I1 /\ StoreAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,StoreAction,Store,Inv22_d756_R1_2_I1
  \* (Inv22_d756_R1_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv22_d756_R1_2_I1 /\ SendReqSAction => Inv22_d756_R1_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv22_d756_R1_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_e00a_R5_0_I1
THEOREM L_18 == TypeOK /\ Inv1_eb94_R7_0_I1 /\ Inv11_e00a_R5_0_I1 /\ Next => Inv11_e00a_R5_0_I1'
  <1>. USE A0,A1
  \* (Inv11_e00a_R5_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv11_e00a_R5_0_I1 /\ SendReqEAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv11_e00a_R5_0_I1 /\ RecvReqSAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv11_e00a_R5_0_I1 /\ RecvReqEAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv11_e00a_R5_0_I1 /\ SendInvAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_e00a_R5_0_I1 /\ SendInvAckAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1_eb94_R7_0_I1 /\ Inv11_e00a_R5_0_I1 /\ RecvInvAckAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,Inv1_eb94_R7_0_I1,RecvInvAckAction,RecvInvAck,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv11_e00a_R5_0_I1 /\ SendGntSAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv11_e00a_R5_0_I1 /\ SendGntEAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_e00a_R5_0_I1 /\ RecvGntSAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv11_e00a_R5_0_I1 /\ RecvGntEAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv11_e00a_R5_0_I1 /\ StoreAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,StoreAction,Store,Inv11_e00a_R5_0_I1
  \* (Inv11_e00a_R5_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv11_e00a_R5_0_I1 /\ SendReqSAction => Inv11_e00a_R5_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv11_e00a_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv12_4ccb_R5_1_I1
THEOREM L_19 == TypeOK /\ Inv1_eb94_R7_0_I1 /\ Inv12_4ccb_R5_1_I1 /\ Next => Inv12_4ccb_R5_1_I1'
  <1>. USE A0,A1
  \* (Inv12_4ccb_R5_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ SendReqEAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ RecvReqSAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ RecvReqEAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ SendInvAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ SendInvAckAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1_eb94_R7_0_I1 /\ Inv12_4ccb_R5_1_I1 /\ RecvInvAckAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,Inv1_eb94_R7_0_I1,RecvInvAckAction,RecvInvAck,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ SendGntSAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ SendGntEAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ RecvGntSAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ RecvGntEAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ StoreAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,StoreAction,Store,Inv12_4ccb_R5_1_I1
  \* (Inv12_4ccb_R5_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv12_4ccb_R5_1_I1 /\ SendReqSAction => Inv12_4ccb_R5_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv12_4ccb_R5_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_8267_R5_2_I1
THEOREM L_20 == TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv11_c03f_R12_0_I1 /\ Inv10_8267_R5_2_I1 /\ Next => Inv10_8267_R5_2_I1'
  <1>. USE A0,A1
  \* (Inv10_8267_R5_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv10_8267_R5_2_I1 /\ SendReqEAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv10_8267_R5_2_I1 /\ RecvReqSAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv10_8267_R5_2_I1 /\ RecvReqEAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_8267_R5_2_I1 /\ SendInvAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv10_8267_R5_2_I1 /\ SendInvAckAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_8267_R5_2_I1 /\ RecvInvAckAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv10_8267_R5_2_I1 /\ SendGntSAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv10_8267_R5_2_I1 /\ SendGntEAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv10_8267_R5_2_I1 /\ RecvGntSAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,Inv11_c03f_R12_0_I1,RecvGntSAction,RecvGntS,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv10_8267_R5_2_I1 /\ RecvGntEAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,Inv11_c03f_R12_0_I1,RecvGntEAction,RecvGntE,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv10_8267_R5_2_I1 /\ StoreAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,StoreAction,Store,Inv10_8267_R5_2_I1
  \* (Inv10_8267_R5_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv10_8267_R5_2_I1 /\ SendReqSAction => Inv10_8267_R5_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv10_8267_R5_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv7_7199_R6_1_I1
THEOREM L_21 == TypeOK /\ Inv8923_9eca_R13_1_I2 /\ Inv15_5b11_R8_0_I1 /\ Inv7_7199_R6_1_I1 /\ Next => Inv7_7199_R6_1_I1'
  <1>. USE A0,A1
  \* (Inv7_7199_R6_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv7_7199_R6_1_I1 /\ SendReqEAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv7_7199_R6_1_I1 /\ RecvReqSAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv7_7199_R6_1_I1 /\ RecvReqEAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv7_7199_R6_1_I1 /\ SendInvAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ Inv7_7199_R6_1_I1 /\ SendInvAckAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,Inv8923_9eca_R13_1_I2,SendInvAckAction,SendInvAck,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv7_7199_R6_1_I1 /\ RecvInvAckAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv7_7199_R6_1_I1 /\ SendGntSAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv7_7199_R6_1_I1 /\ SendGntEAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv7_7199_R6_1_I1 /\ RecvGntSAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv15_5b11_R8_0_I1 /\ Inv7_7199_R6_1_I1 /\ RecvGntEAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,Inv15_5b11_R8_0_I1,RecvGntEAction,RecvGntE,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv7_7199_R6_1_I1 /\ StoreAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,StoreAction,Store,Inv7_7199_R6_1_I1
  \* (Inv7_7199_R6_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv7_7199_R6_1_I1 /\ SendReqSAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv7_7199_R6_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv15_5b11_R8_0_I1
THEOREM L_22 == TypeOK /\ Inv64_c47d_R16_1_I1 /\ Inv14_9e93_R14_0_I1 /\ Inv15_5b11_R8_0_I1 /\ Next => Inv15_5b11_R8_0_I1'
  <1>. USE A0,A1
  \* (Inv15_5b11_R8_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv15_5b11_R8_0_I1 /\ SendReqEAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv15_5b11_R8_0_I1 /\ RecvReqSAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv15_5b11_R8_0_I1 /\ RecvReqEAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv15_5b11_R8_0_I1 /\ SendInvAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv64_c47d_R16_1_I1 /\ Inv15_5b11_R8_0_I1 /\ SendInvAckAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,Inv64_c47d_R16_1_I1,SendInvAckAction,SendInvAck,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv15_5b11_R8_0_I1 /\ RecvInvAckAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv15_5b11_R8_0_I1 /\ SendGntSAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ Inv15_5b11_R8_0_I1 /\ SendGntEAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,Inv14_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv15_5b11_R8_0_I1 /\ RecvGntSAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv15_5b11_R8_0_I1 /\ RecvGntEAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv15_5b11_R8_0_I1 /\ StoreAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,StoreAction,Store,Inv15_5b11_R8_0_I1
  \* (Inv15_5b11_R8_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv15_5b11_R8_0_I1 /\ SendReqSAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv15_5b11_R8_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv64_c47d_R16_1_I1
THEOREM L_23 == TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ Inv39_7204_R20_0_I1 /\ Inv64_c47d_R16_1_I1 /\ Next => Inv64_c47d_R16_1_I1'
  <1>. USE A0,A1
  \* (Inv64_c47d_R16_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv64_c47d_R16_1_I1 /\ SendReqEAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvReqSAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvReqEAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ Inv64_c47d_R16_1_I1 /\ SendInvAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,Inv6423_fc2f_R3_2_I2,SendInvAction,SendInv,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv64_c47d_R16_1_I1 /\ SendInvAckAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvInvAckAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv64_c47d_R16_1_I1 /\ SendGntSAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv64_c47d_R16_1_I1 /\ SendGntEAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendGntEAction,SendGntE,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvGntSAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvGntEAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv64_c47d_R16_1_I1 /\ StoreAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,StoreAction,Store,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv64_c47d_R16_1_I1 /\ SendReqSAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv64_c47d_R16_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6423_fc2f_R3_2_I2
THEOREM L_24 == TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ Inv9619_4ca8_R9_0_I2 /\ Inv104_0f39_R7_1_I1 /\ Inv6423_fc2f_R3_2_I2 /\ Next => Inv6423_fc2f_R3_2_I2'
  <1>. USE A0,A1
  \* (Inv6423_fc2f_R3_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ SendReqEAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ Inv6423_fc2f_R3_2_I2 /\ RecvReqSAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,Inv9619_4ca8_R9_0_I2,RecvReqSAction,RecvReqS,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ Inv6423_fc2f_R3_2_I2 /\ RecvReqEAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,Inv9619_4ca8_R9_0_I2,RecvReqEAction,RecvReqE,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ SendInvAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ SendInvAckAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ RecvInvAckAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ SendGntSAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv104_0f39_R7_1_I1 /\ Inv6423_fc2f_R3_2_I2 /\ SendGntEAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,Inv104_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ RecvGntSAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ RecvGntEAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ StoreAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,StoreAction,Store,Inv6423_fc2f_R3_2_I2
  \* (Inv6423_fc2f_R3_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ SendReqSAction => Inv6423_fc2f_R3_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv6423_fc2f_R3_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv9619_4ca8_R9_0_I2
THEOREM L_25 == TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv5_a2c7_R3_1_I1 /\ Inv9619_4ca8_R9_0_I2 /\ Next => Inv9619_4ca8_R9_0_I2'
  <1>. USE A0,A1
  \* (Inv9619_4ca8_R9_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ SendReqEAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ RecvReqSAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ RecvReqEAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ SendInvAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ SendInvAckAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ RecvInvAckAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv9619_4ca8_R9_0_I2 /\ SendGntSAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv9619_4ca8_R9_0_I2 /\ SendGntEAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntEAction,SendGntE,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ RecvGntSAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ RecvGntEAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ StoreAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,StoreAction,Store,Inv9619_4ca8_R9_0_I2
  \* (Inv9619_4ca8_R9_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ SendReqSAction => Inv9619_4ca8_R9_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv9619_4ca8_R9_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5_a2c7_R3_1_I1
THEOREM L_26 == TypeOK /\ Inv15_5b11_R8_0_I1 /\ Inv5_a2c7_R3_1_I1 /\ Next => Inv5_a2c7_R3_1_I1'
  <1>. USE A0,A1
  \* (Inv5_a2c7_R3_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ SendReqEAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ RecvReqSAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ RecvReqEAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ SendInvAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ SendInvAckAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv15_5b11_R8_0_I1 /\ Inv5_a2c7_R3_1_I1 /\ RecvInvAckAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,Inv15_5b11_R8_0_I1,RecvInvAckAction,RecvInvAck,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ SendGntSAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ SendGntEAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ RecvGntSAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ RecvGntEAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ StoreAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,StoreAction,Store,Inv5_a2c7_R3_1_I1
  \* (Inv5_a2c7_R3_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ SendReqSAction => Inv5_a2c7_R3_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv5_a2c7_R3_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv104_0f39_R7_1_I1
THEOREM L_27 == TypeOK /\ Inv26_259c_R15_0_I1 /\ Inv104_0f39_R7_1_I1 /\ Next => Inv104_0f39_R7_1_I1'
  <1>. USE A0,A1
  \* (Inv104_0f39_R7_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv104_0f39_R7_1_I1 /\ SendReqEAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv104_0f39_R7_1_I1 /\ RecvReqSAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv104_0f39_R7_1_I1 /\ RecvReqEAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv104_0f39_R7_1_I1 /\ SendInvAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv104_0f39_R7_1_I1 /\ SendInvAckAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv26_259c_R15_0_I1 /\ Inv104_0f39_R7_1_I1 /\ RecvInvAckAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,Inv26_259c_R15_0_I1,RecvInvAckAction,RecvInvAck,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv104_0f39_R7_1_I1 /\ SendGntSAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv104_0f39_R7_1_I1 /\ SendGntEAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv104_0f39_R7_1_I1 /\ RecvGntSAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv104_0f39_R7_1_I1 /\ RecvGntEAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv104_0f39_R7_1_I1 /\ StoreAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,StoreAction,Store,Inv104_0f39_R7_1_I1
  \* (Inv104_0f39_R7_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv104_0f39_R7_1_I1 /\ SendReqSAction => Inv104_0f39_R7_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv104_0f39_R7_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv26_259c_R15_0_I1
THEOREM L_28 == TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv3716_575b_R22_0_I2 /\ Inv76_d564_R22_2_I1 /\ Inv26_259c_R15_0_I1 /\ Next => Inv26_259c_R15_0_I1'
  <1>. USE A0,A1
  \* (Inv26_259c_R15_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv26_259c_R15_0_I1 /\ SendReqEAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv26_259c_R15_0_I1 /\ RecvReqSAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,Inv3716_575b_R22_0_I2,RecvReqSAction,RecvReqS,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv26_259c_R15_0_I1 /\ RecvReqEAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,Inv3716_575b_R22_0_I2,RecvReqEAction,RecvReqE,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv26_259c_R15_0_I1 /\ SendInvAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv76_d564_R22_2_I1 /\ Inv26_259c_R15_0_I1 /\ SendInvAckAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,Inv76_d564_R22_2_I1,SendInvAckAction,SendInvAck,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv26_259c_R15_0_I1 /\ RecvInvAckAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv26_259c_R15_0_I1 /\ SendGntSAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv26_259c_R15_0_I1 /\ SendGntEAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv26_259c_R15_0_I1 /\ RecvGntSAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv26_259c_R15_0_I1 /\ RecvGntEAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv26_259c_R15_0_I1 /\ StoreAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,StoreAction,Store,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv26_259c_R15_0_I1 /\ SendReqSAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv26_259c_R15_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv76_d564_R22_2_I1
THEOREM L_29 == TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv651_b778_R29_2_I2 /\ Inv76_d564_R22_2_I1 /\ Next => Inv76_d564_R22_2_I1'
  <1>. USE A0,A1
  \* (Inv76_d564_R22_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendReqEAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv76_d564_R22_2_I1 /\ RecvReqSAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,Inv651_b778_R29_2_I2,RecvReqSAction,RecvReqS,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv76_d564_R22_2_I1 /\ RecvReqEAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,Inv651_b778_R29_2_I2,RecvReqEAction,RecvReqE,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendInvAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendInvAckAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv76_d564_R22_2_I1 /\ RecvInvAckAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendGntSAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendGntEAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv76_d564_R22_2_I1 /\ RecvGntSAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv76_d564_R22_2_I1 /\ RecvGntEAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv76_d564_R22_2_I1 /\ StoreAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,StoreAction,Store,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendReqSAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv76_d564_R22_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv651_b778_R29_2_I2
THEOREM L_30 == TypeOK /\ Inv1611_1275_R21_1_I2 /\ Inv39_7204_R20_0_I1 /\ Inv651_b778_R29_2_I2 /\ Next => Inv651_b778_R29_2_I2'
  <1>. USE A0,A1
  \* (Inv651_b778_R29_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv651_b778_R29_2_I2 /\ SendReqEAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv651_b778_R29_2_I2 /\ RecvReqSAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv651_b778_R29_2_I2 /\ RecvReqEAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv651_b778_R29_2_I2 /\ SendInvAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv651_b778_R29_2_I2 /\ SendInvAckAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv651_b778_R29_2_I2 /\ RecvInvAckAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1611_1275_R21_1_I2 /\ Inv651_b778_R29_2_I2 /\ SendGntSAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,Inv1611_1275_R21_1_I2,SendGntSAction,SendGntS,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv651_b778_R29_2_I2 /\ SendGntEAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendGntEAction,SendGntE,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv651_b778_R29_2_I2 /\ RecvGntSAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv651_b778_R29_2_I2 /\ RecvGntEAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv651_b778_R29_2_I2 /\ StoreAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,StoreAction,Store,Inv651_b778_R29_2_I2
  \* (Inv651_b778_R29_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv651_b778_R29_2_I2 /\ SendReqSAction => Inv651_b778_R29_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv651_b778_R29_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1611_1275_R21_1_I2
THEOREM L_31 == TypeOK /\ Inv3857_1b30_R28_0_I2 /\ Inv1611_1275_R21_1_I2 /\ Next => Inv1611_1275_R21_1_I2'
  <1>. USE A0,A1
  \* (Inv1611_1275_R21_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1611_1275_R21_1_I2 /\ SendReqEAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv1611_1275_R21_1_I2 /\ RecvReqSAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv1611_1275_R21_1_I2 /\ RecvReqEAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1611_1275_R21_1_I2 /\ SendInvAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1611_1275_R21_1_I2 /\ SendInvAckAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ Inv1611_1275_R21_1_I2 /\ RecvInvAckAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,Inv3857_1b30_R28_0_I2,RecvInvAckAction,RecvInvAck,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1611_1275_R21_1_I2 /\ SendGntSAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv1611_1275_R21_1_I2 /\ SendGntEAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1611_1275_R21_1_I2 /\ RecvGntSAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1611_1275_R21_1_I2 /\ RecvGntEAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv1611_1275_R21_1_I2 /\ StoreAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,StoreAction,Store,Inv1611_1275_R21_1_I2
  \* (Inv1611_1275_R21_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1611_1275_R21_1_I2 /\ SendReqSAction => Inv1611_1275_R21_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1611_1275_R21_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3857_1b30_R28_0_I2
THEOREM L_32 == TypeOK /\ Inv1067_2e74_R36_2_I2 /\ Inv28_f7af_R36_1_I2 /\ Inv8923_9eca_R13_1_I2 /\ Inv39_7204_R20_0_I1 /\ Inv3857_1b30_R28_0_I2 /\ Next => Inv3857_1b30_R28_0_I2'
  <1>. USE A0,A1
  \* (Inv3857_1b30_R28_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ SendReqEAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ RecvReqSAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ RecvReqEAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ Inv3857_1b30_R28_0_I2 /\ SendInvAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,Inv1067_2e74_R36_2_I2,SendInvAction,SendInv,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv28_f7af_R36_1_I2 /\ Inv8923_9eca_R13_1_I2 /\ Inv3857_1b30_R28_0_I2 /\ SendInvAckAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,Inv28_f7af_R36_1_I2,Inv8923_9eca_R13_1_I2,SendInvAckAction,SendInvAck,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ RecvInvAckAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ SendGntSAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv3857_1b30_R28_0_I2 /\ SendGntEAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendGntEAction,SendGntE,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ RecvGntSAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ RecvGntEAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ StoreAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,StoreAction,Store,Inv3857_1b30_R28_0_I2
  \* (Inv3857_1b30_R28_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv3857_1b30_R28_0_I2 /\ SendReqSAction => Inv3857_1b30_R28_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3857_1b30_R28_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv28_f7af_R36_1_I2
THEOREM L_33 == TypeOK /\ Inv50_ba79_R27_1_I1 /\ Inv1511_683a_R35_0_I2 /\ Inv39_7204_R20_0_I1 /\ Inv28_f7af_R36_1_I2 /\ Next => Inv28_f7af_R36_1_I2'
  <1>. USE A0,A1
  \* (Inv28_f7af_R36_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv28_f7af_R36_1_I2 /\ SendReqEAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv28_f7af_R36_1_I2 /\ RecvReqSAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv28_f7af_R36_1_I2 /\ RecvReqEAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv50_ba79_R27_1_I1 /\ Inv1511_683a_R35_0_I2 /\ Inv28_f7af_R36_1_I2 /\ SendInvAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,Inv50_ba79_R27_1_I1,Inv1511_683a_R35_0_I2,SendInvAction,SendInv,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv28_f7af_R36_1_I2 /\ SendInvAckAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv28_f7af_R36_1_I2 /\ RecvInvAckAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv28_f7af_R36_1_I2 /\ SendGntSAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv28_f7af_R36_1_I2 /\ SendGntEAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendGntEAction,SendGntE,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv28_f7af_R36_1_I2 /\ RecvGntSAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv28_f7af_R36_1_I2 /\ RecvGntEAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv28_f7af_R36_1_I2 /\ StoreAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,StoreAction,Store,Inv28_f7af_R36_1_I2
  \* (Inv28_f7af_R36_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv28_f7af_R36_1_I2 /\ SendReqSAction => Inv28_f7af_R36_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv28_f7af_R36_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1511_683a_R35_0_I2
THEOREM L_34 == TypeOK /\ Inv2445_d313_R39_0_I4 /\ Inv2445_d313_R39_0_I4 /\ Inv76_d564_R22_2_I1 /\ Inv1511_683a_R35_0_I2 /\ Next => Inv1511_683a_R35_0_I2'
  <1>. USE A0,A1
  \* (Inv1511_683a_R35_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1511_683a_R35_0_I2 /\ SendReqEAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2445_d313_R39_0_I4 /\ Inv1511_683a_R35_0_I2 /\ RecvReqSAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,Inv2445_d313_R39_0_I4,RecvReqSAction,RecvReqS,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2445_d313_R39_0_I4 /\ Inv1511_683a_R35_0_I2 /\ RecvReqEAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,Inv2445_d313_R39_0_I4,RecvReqEAction,RecvReqE,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1511_683a_R35_0_I2 /\ SendInvAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv76_d564_R22_2_I1 /\ Inv1511_683a_R35_0_I2 /\ SendInvAckAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,Inv76_d564_R22_2_I1,SendInvAckAction,SendInvAck,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1511_683a_R35_0_I2 /\ RecvInvAckAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1511_683a_R35_0_I2 /\ SendGntSAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv1511_683a_R35_0_I2 /\ SendGntEAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1511_683a_R35_0_I2 /\ RecvGntSAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1511_683a_R35_0_I2 /\ RecvGntEAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv1511_683a_R35_0_I2 /\ StoreAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,StoreAction,Store,Inv1511_683a_R35_0_I2
  \* (Inv1511_683a_R35_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1511_683a_R35_0_I2 /\ SendReqSAction => Inv1511_683a_R35_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1511_683a_R35_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2445_d313_R39_0_I4
THEOREM L_35 == TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv654_d73e_R42_0_I4 /\ Inv2445_d313_R39_0_I4 /\ Next => Inv2445_d313_R39_0_I4'
  <1>. USE A0,A1
  \* (Inv2445_d313_R39_0_I4,SendReqEAction)
  <1>1. TypeOK /\ Inv2445_d313_R39_0_I4 /\ SendReqEAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,RecvReqSAction)
  <1>2. TypeOK /\ Inv2445_d313_R39_0_I4 /\ RecvReqSAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,RecvReqEAction)
  <1>3. TypeOK /\ Inv2445_d313_R39_0_I4 /\ RecvReqEAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,SendInvAction)
  <1>4. TypeOK /\ Inv2445_d313_R39_0_I4 /\ SendInvAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,SendInvAction,SendInv,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,SendInvAckAction)
  <1>5. TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv2445_d313_R39_0_I4 /\ SendInvAckAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,Inv651_b778_R29_2_I2,SendInvAckAction,SendInvAck,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2445_d313_R39_0_I4 /\ RecvInvAckAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,SendGntSAction)
  <1>7. TypeOK /\ Inv654_d73e_R42_0_I4 /\ Inv2445_d313_R39_0_I4 /\ SendGntSAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,Inv654_d73e_R42_0_I4,SendGntSAction,SendGntS,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,SendGntEAction)
  <1>8. TypeOK /\ Inv2445_d313_R39_0_I4 /\ SendGntEAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,RecvGntSAction)
  <1>9. TypeOK /\ Inv2445_d313_R39_0_I4 /\ RecvGntSAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,RecvGntEAction)
  <1>10. TypeOK /\ Inv2445_d313_R39_0_I4 /\ RecvGntEAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,StoreAction)
  <1>11. TypeOK /\ Inv2445_d313_R39_0_I4 /\ StoreAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,StoreAction,Store,Inv2445_d313_R39_0_I4
  \* (Inv2445_d313_R39_0_I4,SendReqSAction)
  <1>12. TypeOK /\ Inv2445_d313_R39_0_I4 /\ SendReqSAction => Inv2445_d313_R39_0_I4' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2445_d313_R39_0_I4
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv654_d73e_R42_0_I4
THEOREM L_36 == TypeOK /\ Inv2445_d313_R39_0_I4 /\ Inv12_513a_R2_1_I1 /\ Inv1611_1275_R21_1_I2 /\ Inv2246_d6a1_R44_1_I3 /\ Inv5_a2c7_R3_1_I1 /\ Inv654_d73e_R42_0_I4 /\ Next => Inv654_d73e_R42_0_I4'
  <1>. USE A0,A1
  \* (Inv654_d73e_R42_0_I4,SendReqEAction)
  <1>1. TypeOK /\ Inv654_d73e_R42_0_I4 /\ SendReqEAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,SendReqEAction,SendReqE,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,RecvReqSAction)
  <1>2. TypeOK /\ Inv2445_d313_R39_0_I4 /\ Inv12_513a_R2_1_I1 /\ Inv654_d73e_R42_0_I4 /\ RecvReqSAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,Inv2445_d313_R39_0_I4,Inv12_513a_R2_1_I1,RecvReqSAction,RecvReqS,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,RecvReqEAction)
  <1>3. TypeOK /\ Inv654_d73e_R42_0_I4 /\ RecvReqEAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,SendInvAction)
  <1>4. TypeOK /\ Inv654_d73e_R42_0_I4 /\ SendInvAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,SendInvAction,SendInv,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,SendInvAckAction)
  <1>5. TypeOK /\ Inv1611_1275_R21_1_I2 /\ Inv654_d73e_R42_0_I4 /\ SendInvAckAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,Inv1611_1275_R21_1_I2,SendInvAckAction,SendInvAck,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ Inv654_d73e_R42_0_I4 /\ RecvInvAckAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,Inv2246_d6a1_R44_1_I3,RecvInvAckAction,RecvInvAck,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,SendGntSAction)
  <1>7. TypeOK /\ Inv654_d73e_R42_0_I4 /\ SendGntSAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,SendGntSAction,SendGntS,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,SendGntEAction)
  <1>8. TypeOK /\ Inv654_d73e_R42_0_I4 /\ SendGntEAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,SendGntEAction,SendGntE,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,RecvGntSAction)
  <1>9. TypeOK /\ Inv654_d73e_R42_0_I4 /\ RecvGntSAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,RecvGntEAction)
  <1>10. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv654_d73e_R42_0_I4 /\ RecvGntEAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,RecvGntEAction,RecvGntE,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,StoreAction)
  <1>11. TypeOK /\ Inv654_d73e_R42_0_I4 /\ StoreAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,StoreAction,Store,Inv654_d73e_R42_0_I4
  \* (Inv654_d73e_R42_0_I4,SendReqSAction)
  <1>12. TypeOK /\ Inv654_d73e_R42_0_I4 /\ SendReqSAction => Inv654_d73e_R42_0_I4' BY DEF TypeOK,SendReqSAction,SendReqS,Inv654_d73e_R42_0_I4
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2246_d6a1_R44_1_I3
THEOREM L_37 == TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv28_f7af_R36_1_I2 /\ Inv6436_bea9_R25_1_I2 /\ Inv14_9e93_R14_0_I1 /\ Inv2246_d6a1_R44_1_I3 /\ Next => Inv2246_d6a1_R44_1_I3'
  <1>. USE A0,A1
  \* (Inv2246_d6a1_R44_1_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ SendReqEAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ RecvReqSAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ RecvReqEAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,SendInvAction)
  <1>4. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ SendInvAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv28_f7af_R36_1_I2 /\ Inv6436_bea9_R25_1_I2 /\ Inv2246_d6a1_R44_1_I3 /\ SendInvAckAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,Inv1_85ad_R3_0_I1,Inv28_f7af_R36_1_I2,Inv6436_bea9_R25_1_I2,SendInvAckAction,SendInvAck,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ RecvInvAckAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ SendGntSAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv14_9e93_R14_0_I1 /\ Inv2246_d6a1_R44_1_I3 /\ SendGntEAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,Inv14_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ RecvGntSAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ RecvGntEAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,StoreAction)
  <1>11. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ StoreAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,StoreAction,Store,Inv2246_d6a1_R44_1_I3
  \* (Inv2246_d6a1_R44_1_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv2246_d6a1_R44_1_I3 /\ SendReqSAction => Inv2246_d6a1_R44_1_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2246_d6a1_R44_1_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6436_bea9_R25_1_I2
THEOREM L_38 == TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv12_513a_R2_1_I1 /\ Inv9619_4ca8_R9_0_I2 /\ Inv6436_bea9_R25_1_I2 /\ Next => Inv6436_bea9_R25_1_I2'
  <1>. USE A0,A1
  \* (Inv6436_bea9_R25_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ SendReqEAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ RecvReqSAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ RecvReqEAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ SendInvAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ SendInvAckAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ RecvInvAckAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv6436_bea9_R25_1_I2 /\ SendGntSAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,Inv12_513a_R2_1_I1,SendGntSAction,SendGntS,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv6436_bea9_R25_1_I2 /\ SendGntEAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,Inv12_513a_R2_1_I1,SendGntEAction,SendGntE,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ RecvGntSAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv9619_4ca8_R9_0_I2 /\ Inv6436_bea9_R25_1_I2 /\ RecvGntEAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,Inv9619_4ca8_R9_0_I2,RecvGntEAction,RecvGntE,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ StoreAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,StoreAction,Store,Inv6436_bea9_R25_1_I2
  \* (Inv6436_bea9_R25_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ SendReqSAction => Inv6436_bea9_R25_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv6436_bea9_R25_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv12_513a_R2_1_I1
THEOREM L_39 == TypeOK /\ Inv7_7199_R6_1_I1 /\ Inv5_a2c7_R3_1_I1 /\ Inv12_513a_R2_1_I1 /\ Next => Inv12_513a_R2_1_I1'
  <1>. USE A0,A1
  \* (Inv12_513a_R2_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv12_513a_R2_1_I1 /\ SendReqEAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv12_513a_R2_1_I1 /\ RecvReqSAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv12_513a_R2_1_I1 /\ RecvReqEAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv12_513a_R2_1_I1 /\ SendInvAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv12_513a_R2_1_I1 /\ SendInvAckAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv7_7199_R6_1_I1 /\ Inv12_513a_R2_1_I1 /\ RecvInvAckAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,Inv7_7199_R6_1_I1,RecvInvAckAction,RecvInvAck,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv12_513a_R2_1_I1 /\ SendGntSAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv12_513a_R2_1_I1 /\ SendGntEAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv12_513a_R2_1_I1 /\ RecvGntSAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv12_513a_R2_1_I1 /\ RecvGntEAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,RecvGntEAction,RecvGntE,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv12_513a_R2_1_I1 /\ StoreAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,StoreAction,Store,Inv12_513a_R2_1_I1
  \* (Inv12_513a_R2_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv12_513a_R2_1_I1 /\ SendReqSAction => Inv12_513a_R2_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv12_513a_R2_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv8923_9eca_R13_1_I2
THEOREM L_40 == TypeOK /\ Inv3306_6920_R19_1_I2 /\ Inv64_c47d_R16_1_I1 /\ Inv8923_9eca_R13_1_I2 /\ Next => Inv8923_9eca_R13_1_I2'
  <1>. USE A0,A1
  \* (Inv8923_9eca_R13_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ SendReqEAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ RecvReqSAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ RecvReqEAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv3306_6920_R19_1_I2 /\ Inv8923_9eca_R13_1_I2 /\ SendInvAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,Inv3306_6920_R19_1_I2,SendInvAction,SendInv,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ SendInvAckAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ RecvInvAckAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ SendGntSAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ SendGntEAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ RecvGntSAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv64_c47d_R16_1_I1 /\ Inv8923_9eca_R13_1_I2 /\ RecvGntEAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,Inv64_c47d_R16_1_I1,RecvGntEAction,RecvGntE,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ StoreAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,StoreAction,Store,Inv8923_9eca_R13_1_I2
  \* (Inv8923_9eca_R13_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv8923_9eca_R13_1_I2 /\ SendReqSAction => Inv8923_9eca_R13_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv8923_9eca_R13_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3306_6920_R19_1_I2
THEOREM L_41 == TypeOK /\ Inv6436_bea9_R25_1_I2 /\ Inv6436_bea9_R25_1_I2 /\ Inv6423_fc2f_R3_2_I2 /\ Inv3306_6920_R19_1_I2 /\ Next => Inv3306_6920_R19_1_I2'
  <1>. USE A0,A1
  \* (Inv3306_6920_R19_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv3306_6920_R19_1_I2 /\ SendReqEAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ Inv3306_6920_R19_1_I2 /\ RecvReqSAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,Inv6436_bea9_R25_1_I2,RecvReqSAction,RecvReqS,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv6436_bea9_R25_1_I2 /\ Inv3306_6920_R19_1_I2 /\ RecvReqEAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,Inv6436_bea9_R25_1_I2,RecvReqEAction,RecvReqE,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv3306_6920_R19_1_I2 /\ SendInvAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv3306_6920_R19_1_I2 /\ SendInvAckAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3306_6920_R19_1_I2 /\ RecvInvAckAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv3306_6920_R19_1_I2 /\ SendGntSAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv3306_6920_R19_1_I2 /\ SendGntEAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv3306_6920_R19_1_I2 /\ RecvGntSAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv6423_fc2f_R3_2_I2 /\ Inv3306_6920_R19_1_I2 /\ RecvGntEAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,Inv6423_fc2f_R3_2_I2,RecvGntEAction,RecvGntE,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv3306_6920_R19_1_I2 /\ StoreAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,StoreAction,Store,Inv3306_6920_R19_1_I2
  \* (Inv3306_6920_R19_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv3306_6920_R19_1_I2 /\ SendReqSAction => Inv3306_6920_R19_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3306_6920_R19_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1067_2e74_R36_2_I2
THEOREM L_42 == TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv3716_575b_R22_0_I2 /\ Inv100_1def_R41_3_I1 /\ Inv50_ba79_R27_1_I1 /\ Inv45_2bf0_R27_1_I1 /\ Inv3306_6920_R19_1_I2 /\ Inv104_0f39_R7_1_I1 /\ Inv1067_2e74_R36_2_I2 /\ Next => Inv1067_2e74_R36_2_I2'
  <1>. USE A0,A1
  \* (Inv1067_2e74_R36_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ SendReqEAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv1067_2e74_R36_2_I2 /\ RecvReqSAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,Inv3716_575b_R22_0_I2,RecvReqSAction,RecvReqS,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv3716_575b_R22_0_I2 /\ Inv1067_2e74_R36_2_I2 /\ RecvReqEAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,Inv3716_575b_R22_0_I2,RecvReqEAction,RecvReqE,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ SendInvAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv100_1def_R41_3_I1 /\ Inv50_ba79_R27_1_I1 /\ Inv45_2bf0_R27_1_I1 /\ Inv3306_6920_R19_1_I2 /\ Inv1067_2e74_R36_2_I2 /\ SendInvAckAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,Inv100_1def_R41_3_I1,Inv50_ba79_R27_1_I1,Inv45_2bf0_R27_1_I1,Inv3306_6920_R19_1_I2,SendInvAckAction,SendInvAck,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ RecvInvAckAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ SendGntSAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv104_0f39_R7_1_I1 /\ Inv1067_2e74_R36_2_I2 /\ SendGntEAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,Inv104_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ RecvGntSAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ RecvGntEAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ StoreAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,StoreAction,Store,Inv1067_2e74_R36_2_I2
  \* (Inv1067_2e74_R36_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1067_2e74_R36_2_I2 /\ SendReqSAction => Inv1067_2e74_R36_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1067_2e74_R36_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv100_1def_R41_3_I1
THEOREM L_43 == TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv651_b778_R29_2_I2 /\ Inv100_1def_R41_3_I1 /\ Next => Inv100_1def_R41_3_I1'
  <1>. USE A0,A1
  \* (Inv100_1def_R41_3_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv100_1def_R41_3_I1 /\ SendReqEAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv100_1def_R41_3_I1 /\ RecvReqSAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,Inv651_b778_R29_2_I2,RecvReqSAction,RecvReqS,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv651_b778_R29_2_I2 /\ Inv100_1def_R41_3_I1 /\ RecvReqEAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,Inv651_b778_R29_2_I2,RecvReqEAction,RecvReqE,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,SendInvAction)
  <1>4. TypeOK /\ Inv100_1def_R41_3_I1 /\ SendInvAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv100_1def_R41_3_I1 /\ SendInvAckAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv100_1def_R41_3_I1 /\ RecvInvAckAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv100_1def_R41_3_I1 /\ SendGntSAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv100_1def_R41_3_I1 /\ SendGntEAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv100_1def_R41_3_I1 /\ RecvGntSAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv100_1def_R41_3_I1 /\ RecvGntEAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,StoreAction)
  <1>11. TypeOK /\ Inv100_1def_R41_3_I1 /\ StoreAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,StoreAction,Store,Inv100_1def_R41_3_I1
  \* (Inv100_1def_R41_3_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv100_1def_R41_3_I1 /\ SendReqSAction => Inv100_1def_R41_3_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv100_1def_R41_3_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv45_2bf0_R27_1_I1
THEOREM L_44 == TypeOK /\ Inv1511_683a_R35_0_I2 /\ Inv45_2bf0_R27_1_I1 /\ Next => Inv45_2bf0_R27_1_I1'
  <1>. USE A0,A1
  \* (Inv45_2bf0_R27_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ SendReqEAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ RecvReqSAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ RecvReqEAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv1511_683a_R35_0_I2 /\ Inv45_2bf0_R27_1_I1 /\ SendInvAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,Inv1511_683a_R35_0_I2,SendInvAction,SendInv,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ SendInvAckAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ RecvInvAckAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ SendGntSAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ SendGntEAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ RecvGntSAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ RecvGntEAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ StoreAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,StoreAction,Store,Inv45_2bf0_R27_1_I1
  \* (Inv45_2bf0_R27_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv45_2bf0_R27_1_I1 /\ SendReqSAction => Inv45_2bf0_R27_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv45_2bf0_R27_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv32_1336_R1_1_I1
THEOREM L_45 == TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv32_1336_R1_1_I1 /\ Next => Inv32_1336_R1_1_I1'
  <1>. USE A0,A1
  \* (Inv32_1336_R1_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv32_1336_R1_1_I1 /\ SendReqEAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv32_1336_R1_1_I1 /\ RecvReqSAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv32_1336_R1_1_I1 /\ RecvReqEAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv32_1336_R1_1_I1 /\ SendInvAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv32_1336_R1_1_I1 /\ SendInvAckAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv32_1336_R1_1_I1 /\ RecvInvAckAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv32_1336_R1_1_I1 /\ SendGntSAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv32_1336_R1_1_I1 /\ SendGntEAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv32_1336_R1_1_I1 /\ RecvGntSAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv32_1336_R1_1_I1 /\ RecvGntEAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv32_1336_R1_1_I1 /\ StoreAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,StoreAction,Store,Inv32_1336_R1_1_I1
  \* (Inv32_1336_R1_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv32_1336_R1_1_I1 /\ SendReqSAction => Inv32_1336_R1_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv32_1336_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_3662_R0_1_I1
THEOREM L_46 == TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv32_1336_R1_1_I1 /\ Inv10_3662_R0_1_I1 /\ Next => Inv10_3662_R0_1_I1'
  <1>. USE A0,A1
  \* (Inv10_3662_R0_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv10_3662_R0_1_I1 /\ SendReqEAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv10_3662_R0_1_I1 /\ RecvReqSAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv10_3662_R0_1_I1 /\ RecvReqEAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_3662_R0_1_I1 /\ SendInvAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv10_3662_R0_1_I1 /\ SendInvAckAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_3662_R0_1_I1 /\ RecvInvAckAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv10_3662_R0_1_I1 /\ SendGntSAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,Inv12_513a_R2_1_I1,SendGntSAction,SendGntS,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv10_3662_R0_1_I1 /\ SendGntEAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv10_3662_R0_1_I1 /\ RecvGntSAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv32_1336_R1_1_I1 /\ Inv10_3662_R0_1_I1 /\ RecvGntEAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,Inv32_1336_R1_1_I1,RecvGntEAction,RecvGntE,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv10_3662_R0_1_I1 /\ StoreAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,StoreAction,Store,Inv10_3662_R0_1_I1
  \* (Inv10_3662_R0_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv10_3662_R0_1_I1 /\ SendReqSAction => Inv10_3662_R0_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv10_3662_R0_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1
    <1>0. Init => TypeOK 
      <2> SUFFICES ASSUME Init
                   PROVE  TypeOK
        OBVIOUS
      <2>1. Cache \in [NODE -> CACHE]
        BY DEF Init, TypeOK, IndGlobal
      <2>2. Chan1 \in [NODE -> MSG]
        BY DEF Init, TypeOK, IndGlobal
      <2>3. Chan2 \in [NODE -> MSG]
        BY DEF Init, TypeOK, IndGlobal
      <2>4. Chan3 \in [NODE -> MSG]
        BY DEF Init, TypeOK, IndGlobal
      <2>5. InvSet \in [NODE -> BOOLEAN]
        BY DEF Init, TypeOK, IndGlobal
      <2>6. ShrSet \in [NODE -> BOOLEAN]
        BY DEF Init, TypeOK, IndGlobal
      <2>7. ExGntd \in BOOLEAN
        BY DEF Init, TypeOK, IndGlobal
      <2>8. CurCmd \in MSG_CMD
        BY DEF Init, TypeOK, IndGlobal
      <2>9. CurPtr \in NODE
        BY DEF Init, TypeOK, IndGlobal
      <2>10. MemData \in DATA
        BY DEF Init, TypeOK, IndGlobal
      <2>11. AuxData \in DATA
        BY DEF Init, TypeOK, IndGlobal
      <2>12. QED
        BY <2>1, <2>10, <2>11, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv122_03a2_R0_0_I1 BY DEF Init, Inv122_03a2_R0_0_I1, IndGlobal
    <1>3. Init => Inv5427_0d22_R1_0_I2 BY DEF Init, Inv5427_0d22_R1_0_I2, IndGlobal
    <1>4. Init => Inv1_85ad_R3_0_I1 BY DEF Init, Inv1_85ad_R3_0_I1, IndGlobal
    <1>5. Init => Inv1_eb94_R7_0_I1 BY DEF Init, Inv1_eb94_R7_0_I1, IndGlobal
    <1>6. Init => Inv14_9e93_R14_0_I1 BY DEF Init, Inv14_9e93_R14_0_I1, IndGlobal
    <1>7. Init => Inv39_7204_R20_0_I1 BY DEF Init, Inv39_7204_R20_0_I1, IndGlobal
    <1>8. Init => Inv20_5035_R26_0_I1 BY DEF Init, Inv20_5035_R26_0_I1, IndGlobal
    <1>9. Init => Inv13_45c1_R14_2_I1 BY DEF Init, Inv13_45c1_R14_2_I1, IndGlobal
    <1>10. Init => Inv3716_575b_R22_0_I2 BY DEF Init, Inv3716_575b_R22_0_I2, IndGlobal
    <1>11. Init => Inv2748_0201_R14_1_I2 BY DEF Init, Inv2748_0201_R14_1_I2, IndGlobal
    <1>12. Init => Inv1036_a1d6_R21_0_I3 BY DEF Init, Inv1036_a1d6_R21_0_I3, IndGlobal
    <1>13. Init => Inv11_c03f_R12_0_I1 BY DEF Init, Inv11_c03f_R12_0_I1, IndGlobal
    <1>14. Init => Inv13_812b_R27_1_I1 BY DEF Init, Inv13_812b_R27_1_I1, IndGlobal
    <1>15. Init => Inv50_ba79_R27_1_I1 BY DEF Init, Inv50_ba79_R27_1_I1, IndGlobal
    <1>16. Init => Inv43_39a8_R34_0_I1 BY DEF Init, Inv43_39a8_R34_0_I1, IndGlobal
    <1>17. Init => Inv22_d756_R1_2_I1 BY DEF Init, Inv22_d756_R1_2_I1, IndGlobal
    <1>18. Init => Inv11_e00a_R5_0_I1 BY DEF Init, Inv11_e00a_R5_0_I1, IndGlobal
    <1>19. Init => Inv12_4ccb_R5_1_I1 BY DEF Init, Inv12_4ccb_R5_1_I1, IndGlobal
    <1>20. Init => Inv10_8267_R5_2_I1 BY DEF Init, Inv10_8267_R5_2_I1, IndGlobal
    <1>21. Init => Inv7_7199_R6_1_I1 BY DEF Init, Inv7_7199_R6_1_I1, IndGlobal
    <1>22. Init => Inv15_5b11_R8_0_I1 BY DEF Init, Inv15_5b11_R8_0_I1, IndGlobal
    <1>23. Init => Inv64_c47d_R16_1_I1 BY DEF Init, Inv64_c47d_R16_1_I1, IndGlobal
    <1>24. Init => Inv6423_fc2f_R3_2_I2 BY DEF Init, Inv6423_fc2f_R3_2_I2, IndGlobal
    <1>25. Init => Inv9619_4ca8_R9_0_I2 BY DEF Init, Inv9619_4ca8_R9_0_I2, IndGlobal
    <1>26. Init => Inv5_a2c7_R3_1_I1 BY DEF Init, Inv5_a2c7_R3_1_I1, IndGlobal
    <1>27. Init => Inv104_0f39_R7_1_I1 BY DEF Init, Inv104_0f39_R7_1_I1, IndGlobal
    <1>28. Init => Inv26_259c_R15_0_I1 BY DEF Init, Inv26_259c_R15_0_I1, IndGlobal
    <1>29. Init => Inv76_d564_R22_2_I1 BY DEF Init, Inv76_d564_R22_2_I1, IndGlobal
    <1>30. Init => Inv651_b778_R29_2_I2 BY DEF Init, Inv651_b778_R29_2_I2, IndGlobal
    <1>31. Init => Inv1611_1275_R21_1_I2 BY DEF Init, Inv1611_1275_R21_1_I2, IndGlobal
    <1>32. Init => Inv3857_1b30_R28_0_I2 BY DEF Init, Inv3857_1b30_R28_0_I2, IndGlobal
    <1>33. Init => Inv28_f7af_R36_1_I2 BY DEF Init, Inv28_f7af_R36_1_I2, IndGlobal
    <1>34. Init => Inv1511_683a_R35_0_I2 BY DEF Init, Inv1511_683a_R35_0_I2, IndGlobal
    <1>35. Init => Inv2445_d313_R39_0_I4 BY DEF Init, Inv2445_d313_R39_0_I4, IndGlobal
    <1>36. Init => Inv654_d73e_R42_0_I4 BY DEF Init, Inv654_d73e_R42_0_I4, IndGlobal
    <1>37. Init => Inv2246_d6a1_R44_1_I3 BY DEF Init, Inv2246_d6a1_R44_1_I3, IndGlobal
    <1>38. Init => Inv6436_bea9_R25_1_I2 BY DEF Init, Inv6436_bea9_R25_1_I2, IndGlobal
    <1>39. Init => Inv12_513a_R2_1_I1 BY DEF Init, Inv12_513a_R2_1_I1, IndGlobal
    <1>40. Init => Inv8923_9eca_R13_1_I2 BY DEF Init, Inv8923_9eca_R13_1_I2, IndGlobal
    <1>41. Init => Inv3306_6920_R19_1_I2 BY DEF Init, Inv3306_6920_R19_1_I2, IndGlobal
    <1>42. Init => Inv1067_2e74_R36_2_I2 BY DEF Init, Inv1067_2e74_R36_2_I2, IndGlobal
    <1>43. Init => Inv100_1def_R41_3_I1 BY DEF Init, Inv100_1def_R41_3_I1, IndGlobal
    <1>44. Init => Inv45_2bf0_R27_1_I1 BY DEF Init, Inv45_2bf0_R27_1_I1, IndGlobal
    <1>45. Init => Inv32_1336_R1_1_I1 BY DEF Init, Inv32_1336_R1_1_I1, IndGlobal
    <1>46. Init => Inv10_3662_R0_1_I1 BY DEF Init, Inv10_3662_R0_1_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36,<1>37,<1>38,<1>39,<1>40,<1>41,<1>42,<1>43,<1>44,<1>45,<1>46 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36,L_37,L_38,L_39,L_40,L_41,L_42,L_43,L_44,L_45,L_46 DEF Next, IndGlobal


====