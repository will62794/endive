------------------------- MODULE GermanCache_IndProofs -------------------------
EXTENDS GermanCache


USE DEF CtrlProp1
USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE

\* Proof Graph Stats
\* ==================
\* seed: 7
\* num proof graph nodes: 46
\* num proof obligations: 552
Safety == CtrlProp1
Inv122_03a2_R0_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Cache[VARJ].State = "I") \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv11_3662_R0_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(Chan2[VARJ].Cmd = "GntS"))
Inv5378_0d22_R1_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "GntE") \/ (~(VARI # VARJ)))
Inv33_1336_R1_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(Chan2[VARJ].Cmd = "GntS"))
Inv22_d756_R1_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((ShrSet[VARI]))
Inv12_513a_R2_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Cache[VARI].State = "E"))
Inv1_85ad_R3_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
Inv5_a2c7_R3_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv6410_fc2f_R3_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))
Inv11_e00a_R5_0_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv12_4ccb_R5_1_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "GntS"))
Inv10_8267_R5_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((Chan3[VARI].Cmd = "Empty"))
Inv7_7199_R6_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Cache[VARJ].State = "E"))
Inv1_eb94_R7_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((Chan3[VARI].Cmd = "Empty"))
Inv111_0f39_R7_1_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(InvSet[VARI]))
Inv15_5b11_R8_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "GntE"))
Inv9560_0995_R9_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(VARI # VARJ)) \/ (~(ShrSet[VARJ]))
Inv11_c03f_R12_0_I1 == \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Empty") \/ ((Chan3[VARJ].Cmd = "Empty"))
Inv40_2bf0_R13_1_I1 == \A VARI \in NODE : ~(Cache[VARI].State = "I") \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv17_9e93_R14_0_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
Inv4424_0201_R14_1_I2 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((CurCmd = "ReqE")) \/ ((ExGntd))
Inv13_45c1_R14_2_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(InvSet[VARI]))
Inv26_259c_R15_0_I1 == \A VARJ \in NODE : (Chan3[VARJ].Cmd = "Empty") \/ (~(InvSet[VARJ]))
Inv64_c47d_R16_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(Chan2[VARJ].Cmd = "Inv"))
Inv4763_b566_R19_0_I2 == \A VARI \in NODE : ~(Cache[VARI].State = "I") \/ (~(Chan2[VARI].Cmd = "Empty") \/ (~(InvSet[VARI])))
Inv39_7204_R20_0_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv1057_089e_R21_0_I3 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd) \/ (~(VARI # VARJ))) \/ ((Chan3[VARJ].Cmd = "Empty"))
Inv2458_2a15_R21_1_I2 == \A VARI \in NODE : (CurCmd = "ReqE") \/ (~(Chan2[VARI].Cmd = "Inv")) \/ ((ExGntd))
Inv4043_dbee_R22_0_I2 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((CurCmd = "ReqE")) \/ ((CurCmd = "ReqS"))
Inv76_d564_R22_2_I1 == \A VARI \in NODE : ~(Chan2[VARI].Cmd = "Inv") \/ (~(InvSet[VARI]))
Inv1103_d53b_R25_0_I4 == \A VARJ \in NODE : (CurCmd = "ReqE") \/ ((InvSet[VARJ])) \/ (~(Chan2[VARJ].Cmd = "Empty")) \/ (~(Cache[VARJ].State = "I")) \/ ((CurCmd = "ReqS")) \/ (~(ShrSet[VARJ]))
Inv20_5035_R26_0_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv13_812b_R27_1_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((Chan3[VARI].Cmd = "InvAck"))
Inv50_ba79_R27_1_I1 == \A VARI \in NODE : ~(Cache[VARI].State = "S") \/ (~(ExGntd))
Inv2146_6e63_R28_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd)) \/ (~(Chan2[VARJ].Cmd = "Inv"))
Inv1149_870b_R29_2_I2 == \A VARJ \in NODE : (CurCmd = "ReqE") \/ ((CurCmd = "ReqS") \/ (~(Chan2[VARJ].Cmd = "Inv")))
Inv957_c432_R31_0_I2 == \A VARI \in NODE : (ExGntd) \/ ((InvSet[VARI] = ShrSet[VARI]) \/ (~(CurCmd = "ReqS")))
Inv43_39a8_R34_0_I1 == \A VARI \in NODE : ~(Chan2[VARI].Cmd = "GntS") \/ (~(ExGntd))
Inv687_881e_R35_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd)) \/ (~(InvSet[VARJ]))
Inv1942_3576_R37_0_I3 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARJ].Cmd = "Empty") \/ ((InvSet[VARI] = ShrSet[VARI]) \/ (~(ExGntd) \/ (~(VARI # VARJ))))
Inv1000_d532_R39_3_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARJ].Cmd = "Inv") \/ (~(InvSet[VARI])) \/ (~(ExGntd))
Inv111_3e57_R40_1_I2 == \A VARI \in NODE : ~(Chan2[VARI].Cmd = "Inv") \/ (~(InvSet[VARI] = ShrSet[VARI]))
Inv848_bea9_R40_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(ShrSet[VARJ])) \/ (~(VARI # VARJ))
Inv23009_51f5_R41_3_I3 == \A VARI \in NODE : \A VARJ \in NODE : ~(ExGntd) \/ (~(InvSet[VARI]) \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ))))
Inv7513_6fbd_R44_0_I3 == \A VARI \in NODE : \A VARJ \in NODE : (InvSet[VARI] = ShrSet[VARI]) \/ (~(ExGntd)) \/ (~(VARI # VARJ)) \/ (~(ShrSet[VARJ]))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv122_03a2_R0_0_I1
  /\ Inv5378_0d22_R1_0_I2
  /\ Inv1_85ad_R3_0_I1
  /\ Inv1_eb94_R7_0_I1
  /\ Inv17_9e93_R14_0_I1
  /\ Inv39_7204_R20_0_I1
  /\ Inv20_5035_R26_0_I1
  /\ Inv13_45c1_R14_2_I1
  /\ Inv4043_dbee_R22_0_I2
  /\ Inv4424_0201_R14_1_I2
  /\ Inv1057_089e_R21_0_I3
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
  /\ Inv6410_fc2f_R3_2_I2
  /\ Inv9560_0995_R9_0_I2
  /\ Inv5_a2c7_R3_1_I1
  /\ Inv111_0f39_R7_1_I1
  /\ Inv26_259c_R15_0_I1
  /\ Inv76_d564_R22_2_I1
  /\ Inv1149_870b_R29_2_I2
  /\ Inv2458_2a15_R21_1_I2
  /\ Inv2146_6e63_R28_0_I2
  /\ Inv40_2bf0_R13_1_I1
  /\ Inv4763_b566_R19_0_I2
  /\ Inv1103_d53b_R25_0_I4
  /\ Inv957_c432_R31_0_I2
  /\ Inv1942_3576_R37_0_I3
  /\ Inv111_3e57_R40_1_I2
  /\ Inv1000_d532_R39_3_I2
  /\ Inv23009_51f5_R41_3_I3
  /\ Inv7513_6fbd_R44_0_I3
  /\ Inv848_bea9_R40_1_I2
  /\ Inv12_513a_R2_1_I1
  /\ Inv687_881e_R35_2_I2
  /\ Inv33_1336_R1_1_I1
  /\ Inv11_3662_R0_1_I1


\* mean in-degree: 2.4347826086956523
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
THEOREM L_1 == TypeOK /\ Inv11_3662_R0_1_I1 /\ Inv122_03a2_R0_0_I1 /\ Safety /\ Next => Safety'
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
  <1>9. TypeOK /\ Inv11_3662_R0_1_I1 /\ Safety /\ RecvGntSAction => Safety' BY DEF TypeOK,Inv11_3662_R0_1_I1,RecvGntSAction,RecvGntS,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,RecvGntEAction)
  <1>10. TypeOK /\ Inv122_03a2_R0_0_I1 /\ Safety /\ RecvGntEAction => Safety' BY DEF TypeOK,Inv122_03a2_R0_0_I1,RecvGntEAction,RecvGntE,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,StoreAction)
  <1>11. TypeOK /\ Safety /\ StoreAction => Safety' BY DEF TypeOK,StoreAction,Store,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
  \* (Safety,SendReqSAction)
  <1>12. TypeOK /\ Safety /\ SendReqSAction => Safety' BY DEF TypeOK,SendReqSAction,SendReqS,Safety,CtrlProp1,MSG,MSG_CMD,CACHE,CACHE_STATE
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv122_03a2_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv22_d756_R1_2_I1 /\ Inv33_1336_R1_1_I1 /\ Inv5378_0d22_R1_0_I2 /\ Inv122_03a2_R0_0_I1 /\ Next => Inv122_03a2_R0_0_I1'
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
  <1>9. TypeOK /\ Inv33_1336_R1_1_I1 /\ Inv122_03a2_R0_0_I1 /\ RecvGntSAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,Inv33_1336_R1_1_I1,RecvGntSAction,RecvGntS,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ Inv122_03a2_R0_0_I1 /\ RecvGntEAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,Inv5378_0d22_R1_0_I2,RecvGntEAction,RecvGntE,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv122_03a2_R0_0_I1 /\ StoreAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,StoreAction,Store,Inv122_03a2_R0_0_I1
  \* (Inv122_03a2_R0_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv122_03a2_R0_0_I1 /\ SendReqSAction => Inv122_03a2_R0_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv122_03a2_R0_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5378_0d22_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ Inv5_a2c7_R3_1_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv5378_0d22_R1_0_I2 /\ Next => Inv5378_0d22_R1_0_I2'
  <1>. USE A0,A1
  \* (Inv5378_0d22_R1_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ SendReqEAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ RecvReqSAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ RecvReqEAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ Inv5378_0d22_R1_0_I2 /\ SendInvAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,Inv6410_fc2f_R3_2_I2,SendInvAction,SendInv,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ SendInvAckAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ RecvInvAckAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv5378_0d22_R1_0_I2 /\ SendGntSAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv5378_0d22_R1_0_I2 /\ SendGntEAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ RecvGntSAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ RecvGntEAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ StoreAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,StoreAction,Store,Inv5378_0d22_R1_0_I2
  \* (Inv5378_0d22_R1_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv5378_0d22_R1_0_I2 /\ SendReqSAction => Inv5378_0d22_R1_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv5378_0d22_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_85ad_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv1_eb94_R7_0_I1 /\ Inv1_85ad_R3_0_I1 /\ Next => Inv1_85ad_R3_0_I1'
  <1>. USE A0,A1
  \* (Inv1_85ad_R3_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendReqEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvReqSAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvReqEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv1_85ad_R3_0_I1 /\ SendInvAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendInvAction,SendInv,Inv1_85ad_R3_0_I1
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
THEOREM L_5 == TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv4424_0201_R14_1_I2 /\ Inv17_9e93_R14_0_I1 /\ Inv1_eb94_R7_0_I1 /\ Next => Inv1_eb94_R7_0_I1'
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
  <1>7. TypeOK /\ Inv4424_0201_R14_1_I2 /\ Inv1_eb94_R7_0_I1 /\ SendGntSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv4424_0201_R14_1_I2,SendGntSAction,SendGntS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ Inv1_eb94_R7_0_I1 /\ SendGntEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv17_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvGntSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvGntEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv1_eb94_R7_0_I1 /\ StoreAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,StoreAction,Store,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendReqSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1_eb94_R7_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv17_9e93_R14_0_I1
THEOREM L_6 == TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv17_9e93_R14_0_I1 /\ Next => Inv17_9e93_R14_0_I1'
  <1>. USE A0,A1
  \* (Inv17_9e93_R14_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv17_9e93_R14_0_I1 /\ SendReqEAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv17_9e93_R14_0_I1 /\ RecvReqSAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv17_9e93_R14_0_I1 /\ RecvReqEAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv17_9e93_R14_0_I1 /\ SendInvAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv17_9e93_R14_0_I1 /\ SendInvAckAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendInvAckAction,SendInvAck,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv17_9e93_R14_0_I1 /\ RecvInvAckAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv17_9e93_R14_0_I1 /\ SendGntSAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ SendGntEAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv17_9e93_R14_0_I1 /\ RecvGntSAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv17_9e93_R14_0_I1 /\ RecvGntEAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv17_9e93_R14_0_I1 /\ StoreAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,StoreAction,Store,Inv17_9e93_R14_0_I1
  \* (Inv17_9e93_R14_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv17_9e93_R14_0_I1 /\ SendReqSAction => Inv17_9e93_R14_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv17_9e93_R14_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv39_7204_R20_0_I1
THEOREM L_7 == TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv20_5035_R26_0_I1 /\ Inv39_7204_R20_0_I1 /\ Next => Inv39_7204_R20_0_I1'
  <1>. USE A0,A1
  \* (Inv39_7204_R20_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv39_7204_R20_0_I1 /\ SendReqEAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv39_7204_R20_0_I1 /\ RecvReqSAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv39_7204_R20_0_I1 /\ RecvReqEAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv39_7204_R20_0_I1
  \* (Inv39_7204_R20_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv39_7204_R20_0_I1 /\ SendInvAction => Inv39_7204_R20_0_I1' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendInvAction,SendInv,Inv39_7204_R20_0_I1
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
THEOREM L_9 == TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv4043_dbee_R22_0_I2 /\ Inv76_d564_R22_2_I1 /\ Inv13_45c1_R14_2_I1 /\ Next => Inv13_45c1_R14_2_I1'
  <1>. USE A0,A1
  \* (Inv13_45c1_R14_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv13_45c1_R14_2_I1 /\ SendReqEAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv13_45c1_R14_2_I1 /\ RecvReqSAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,Inv4043_dbee_R22_0_I2,RecvReqSAction,RecvReqS,Inv13_45c1_R14_2_I1
  \* (Inv13_45c1_R14_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv13_45c1_R14_2_I1 /\ RecvReqEAction => Inv13_45c1_R14_2_I1' BY DEF TypeOK,Inv4043_dbee_R22_0_I2,RecvReqEAction,RecvReqE,Inv13_45c1_R14_2_I1
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


\*** Inv4043_dbee_R22_0_I2
THEOREM L_10 == TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv4424_0201_R14_1_I2 /\ Inv17_9e93_R14_0_I1 /\ Inv4043_dbee_R22_0_I2 /\ Next => Inv4043_dbee_R22_0_I2'
  <1>. USE A0,A1
  \* (Inv4043_dbee_R22_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ SendReqEAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ RecvReqSAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ RecvReqEAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ SendInvAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv4043_dbee_R22_0_I2 /\ SendInvAckAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,Inv1149_870b_R29_2_I2,SendInvAckAction,SendInvAck,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ RecvInvAckAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv4424_0201_R14_1_I2 /\ Inv4043_dbee_R22_0_I2 /\ SendGntSAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,Inv4424_0201_R14_1_I2,SendGntSAction,SendGntS,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ Inv4043_dbee_R22_0_I2 /\ SendGntEAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,Inv17_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ RecvGntSAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ RecvGntEAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ StoreAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,StoreAction,Store,Inv4043_dbee_R22_0_I2
  \* (Inv4043_dbee_R22_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ SendReqSAction => Inv4043_dbee_R22_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv4043_dbee_R22_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4424_0201_R14_1_I2
THEOREM L_11 == TypeOK /\ Inv2458_2a15_R21_1_I2 /\ Inv1057_089e_R21_0_I3 /\ Inv4424_0201_R14_1_I2 /\ Next => Inv4424_0201_R14_1_I2'
  <1>. USE A0,A1
  \* (Inv4424_0201_R14_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv4424_0201_R14_1_I2 /\ SendReqEAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv4424_0201_R14_1_I2 /\ RecvReqSAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv4424_0201_R14_1_I2 /\ RecvReqEAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv4424_0201_R14_1_I2 /\ SendInvAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ Inv4424_0201_R14_1_I2 /\ SendInvAckAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,Inv2458_2a15_R21_1_I2,SendInvAckAction,SendInvAck,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1057_089e_R21_0_I3 /\ Inv4424_0201_R14_1_I2 /\ RecvInvAckAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,Inv1057_089e_R21_0_I3,RecvInvAckAction,RecvInvAck,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv4424_0201_R14_1_I2 /\ SendGntSAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv4424_0201_R14_1_I2 /\ SendGntEAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv4424_0201_R14_1_I2 /\ RecvGntSAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv4424_0201_R14_1_I2 /\ RecvGntEAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv4424_0201_R14_1_I2 /\ StoreAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,StoreAction,Store,Inv4424_0201_R14_1_I2
  \* (Inv4424_0201_R14_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv4424_0201_R14_1_I2 /\ SendReqSAction => Inv4424_0201_R14_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv4424_0201_R14_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1057_089e_R21_0_I3
THEOREM L_12 == TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv13_812b_R27_1_I1 /\ Inv50_ba79_R27_1_I1 /\ Inv7_7199_R6_1_I1 /\ Inv40_2bf0_R13_1_I1 /\ Inv17_9e93_R14_0_I1 /\ Inv1057_089e_R21_0_I3 /\ Next => Inv1057_089e_R21_0_I3'
  <1>. USE A0,A1
  \* (Inv1057_089e_R21_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv1057_089e_R21_0_I3 /\ SendReqEAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv1057_089e_R21_0_I3 /\ RecvReqSAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv1057_089e_R21_0_I3 /\ RecvReqEAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv1057_089e_R21_0_I3 /\ SendInvAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_c03f_R12_0_I1 /\ Inv13_812b_R27_1_I1 /\ Inv50_ba79_R27_1_I1 /\ Inv7_7199_R6_1_I1 /\ Inv40_2bf0_R13_1_I1 /\ Inv1057_089e_R21_0_I3 /\ SendInvAckAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,Inv11_c03f_R12_0_I1,Inv13_812b_R27_1_I1,Inv50_ba79_R27_1_I1,Inv7_7199_R6_1_I1,Inv40_2bf0_R13_1_I1,SendInvAckAction,SendInvAck,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1057_089e_R21_0_I3 /\ RecvInvAckAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv1057_089e_R21_0_I3 /\ SendGntSAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ Inv1057_089e_R21_0_I3 /\ SendGntEAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,Inv17_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv1057_089e_R21_0_I3 /\ RecvGntSAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv1057_089e_R21_0_I3 /\ RecvGntEAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv1057_089e_R21_0_I3 /\ StoreAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,StoreAction,Store,Inv1057_089e_R21_0_I3
  \* (Inv1057_089e_R21_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv1057_089e_R21_0_I3 /\ SendReqSAction => Inv1057_089e_R21_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1057_089e_R21_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_c03f_R12_0_I1
THEOREM L_13 == TypeOK /\ Inv13_45c1_R14_2_I1 /\ Inv4424_0201_R14_1_I2 /\ Inv17_9e93_R14_0_I1 /\ Inv11_c03f_R12_0_I1 /\ Next => Inv11_c03f_R12_0_I1'
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
  <1>7. TypeOK /\ Inv4424_0201_R14_1_I2 /\ Inv11_c03f_R12_0_I1 /\ SendGntSAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,Inv4424_0201_R14_1_I2,SendGntSAction,SendGntS,Inv11_c03f_R12_0_I1
  \* (Inv11_c03f_R12_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ Inv11_c03f_R12_0_I1 /\ SendGntEAction => Inv11_c03f_R12_0_I1' BY DEF TypeOK,Inv17_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv11_c03f_R12_0_I1
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
THEOREM L_21 == TypeOK /\ Safety /\ Inv40_2bf0_R13_1_I1 /\ Inv15_5b11_R8_0_I1 /\ Inv7_7199_R6_1_I1 /\ Next => Inv7_7199_R6_1_I1'
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
  <1>5. TypeOK /\ Safety /\ Inv40_2bf0_R13_1_I1 /\ Inv7_7199_R6_1_I1 /\ SendInvAckAction => Inv7_7199_R6_1_I1' BY DEF TypeOK,Safety,Inv40_2bf0_R13_1_I1,SendInvAckAction,SendInvAck,Inv7_7199_R6_1_I1
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
THEOREM L_22 == TypeOK /\ Inv64_c47d_R16_1_I1 /\ Inv17_9e93_R14_0_I1 /\ Inv15_5b11_R8_0_I1 /\ Next => Inv15_5b11_R8_0_I1'
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
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ Inv15_5b11_R8_0_I1 /\ SendGntEAction => Inv15_5b11_R8_0_I1' BY DEF TypeOK,Inv17_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv15_5b11_R8_0_I1
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
THEOREM L_23 == TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ Inv39_7204_R20_0_I1 /\ Inv64_c47d_R16_1_I1 /\ Next => Inv64_c47d_R16_1_I1'
  <1>. USE A0,A1
  \* (Inv64_c47d_R16_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv64_c47d_R16_1_I1 /\ SendReqEAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvReqSAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv64_c47d_R16_1_I1 /\ RecvReqEAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv64_c47d_R16_1_I1
  \* (Inv64_c47d_R16_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ Inv64_c47d_R16_1_I1 /\ SendInvAction => Inv64_c47d_R16_1_I1' BY DEF TypeOK,Inv6410_fc2f_R3_2_I2,SendInvAction,SendInv,Inv64_c47d_R16_1_I1
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


\*** Inv6410_fc2f_R3_2_I2
THEOREM L_24 == TypeOK /\ Inv9560_0995_R9_0_I2 /\ Inv9560_0995_R9_0_I2 /\ Inv111_0f39_R7_1_I1 /\ Inv6410_fc2f_R3_2_I2 /\ Next => Inv6410_fc2f_R3_2_I2'
  <1>. USE A0,A1
  \* (Inv6410_fc2f_R3_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ SendReqEAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv9560_0995_R9_0_I2 /\ Inv6410_fc2f_R3_2_I2 /\ RecvReqSAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,Inv9560_0995_R9_0_I2,RecvReqSAction,RecvReqS,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv9560_0995_R9_0_I2 /\ Inv6410_fc2f_R3_2_I2 /\ RecvReqEAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,Inv9560_0995_R9_0_I2,RecvReqEAction,RecvReqE,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ SendInvAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ SendInvAckAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ RecvInvAckAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ SendGntSAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv6410_fc2f_R3_2_I2 /\ SendGntEAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ RecvGntSAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ RecvGntEAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ StoreAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,StoreAction,Store,Inv6410_fc2f_R3_2_I2
  \* (Inv6410_fc2f_R3_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv6410_fc2f_R3_2_I2 /\ SendReqSAction => Inv6410_fc2f_R3_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv6410_fc2f_R3_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv9560_0995_R9_0_I2
THEOREM L_25 == TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv5_a2c7_R3_1_I1 /\ Inv9560_0995_R9_0_I2 /\ Next => Inv9560_0995_R9_0_I2'
  <1>. USE A0,A1
  \* (Inv9560_0995_R9_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv9560_0995_R9_0_I2 /\ SendReqEAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv9560_0995_R9_0_I2 /\ RecvReqSAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv9560_0995_R9_0_I2 /\ RecvReqEAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv9560_0995_R9_0_I2 /\ SendInvAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv9560_0995_R9_0_I2 /\ SendInvAckAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv9560_0995_R9_0_I2 /\ RecvInvAckAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv9560_0995_R9_0_I2 /\ SendGntSAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv9560_0995_R9_0_I2 /\ SendGntEAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntEAction,SendGntE,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv9560_0995_R9_0_I2 /\ RecvGntSAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv9560_0995_R9_0_I2 /\ RecvGntEAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv9560_0995_R9_0_I2 /\ StoreAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,StoreAction,Store,Inv9560_0995_R9_0_I2
  \* (Inv9560_0995_R9_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv9560_0995_R9_0_I2 /\ SendReqSAction => Inv9560_0995_R9_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv9560_0995_R9_0_I2
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


\*** Inv111_0f39_R7_1_I1
THEOREM L_27 == TypeOK /\ Inv26_259c_R15_0_I1 /\ Inv111_0f39_R7_1_I1 /\ Next => Inv111_0f39_R7_1_I1'
  <1>. USE A0,A1
  \* (Inv111_0f39_R7_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv111_0f39_R7_1_I1 /\ SendReqEAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv111_0f39_R7_1_I1 /\ RecvReqSAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv111_0f39_R7_1_I1 /\ RecvReqEAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv111_0f39_R7_1_I1 /\ SendInvAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv111_0f39_R7_1_I1 /\ SendInvAckAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv26_259c_R15_0_I1 /\ Inv111_0f39_R7_1_I1 /\ RecvInvAckAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,Inv26_259c_R15_0_I1,RecvInvAckAction,RecvInvAck,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv111_0f39_R7_1_I1 /\ SendGntSAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv111_0f39_R7_1_I1 /\ SendGntEAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv111_0f39_R7_1_I1 /\ RecvGntSAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv111_0f39_R7_1_I1 /\ RecvGntEAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv111_0f39_R7_1_I1 /\ StoreAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,StoreAction,Store,Inv111_0f39_R7_1_I1
  \* (Inv111_0f39_R7_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv111_0f39_R7_1_I1 /\ SendReqSAction => Inv111_0f39_R7_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv111_0f39_R7_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv26_259c_R15_0_I1
THEOREM L_28 == TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv4043_dbee_R22_0_I2 /\ Inv76_d564_R22_2_I1 /\ Inv26_259c_R15_0_I1 /\ Next => Inv26_259c_R15_0_I1'
  <1>. USE A0,A1
  \* (Inv26_259c_R15_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv26_259c_R15_0_I1 /\ SendReqEAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv26_259c_R15_0_I1 /\ RecvReqSAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,Inv4043_dbee_R22_0_I2,RecvReqSAction,RecvReqS,Inv26_259c_R15_0_I1
  \* (Inv26_259c_R15_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv26_259c_R15_0_I1 /\ RecvReqEAction => Inv26_259c_R15_0_I1' BY DEF TypeOK,Inv4043_dbee_R22_0_I2,RecvReqEAction,RecvReqE,Inv26_259c_R15_0_I1
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
THEOREM L_29 == TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv1149_870b_R29_2_I2 /\ Inv76_d564_R22_2_I1 /\ Next => Inv76_d564_R22_2_I1'
  <1>. USE A0,A1
  \* (Inv76_d564_R22_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv76_d564_R22_2_I1 /\ SendReqEAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv76_d564_R22_2_I1 /\ RecvReqSAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,Inv1149_870b_R29_2_I2,RecvReqSAction,RecvReqS,Inv76_d564_R22_2_I1
  \* (Inv76_d564_R22_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv76_d564_R22_2_I1 /\ RecvReqEAction => Inv76_d564_R22_2_I1' BY DEF TypeOK,Inv1149_870b_R29_2_I2,RecvReqEAction,RecvReqE,Inv76_d564_R22_2_I1
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


\*** Inv1149_870b_R29_2_I2
THEOREM L_30 == TypeOK /\ Inv2458_2a15_R21_1_I2 /\ Inv39_7204_R20_0_I1 /\ Inv1149_870b_R29_2_I2 /\ Next => Inv1149_870b_R29_2_I2'
  <1>. USE A0,A1
  \* (Inv1149_870b_R29_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1149_870b_R29_2_I2 /\ SendReqEAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv1149_870b_R29_2_I2 /\ RecvReqSAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv1149_870b_R29_2_I2 /\ RecvReqEAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1149_870b_R29_2_I2 /\ SendInvAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1149_870b_R29_2_I2 /\ SendInvAckAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1149_870b_R29_2_I2 /\ RecvInvAckAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ Inv1149_870b_R29_2_I2 /\ SendGntSAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,Inv2458_2a15_R21_1_I2,SendGntSAction,SendGntS,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv1149_870b_R29_2_I2 /\ SendGntEAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendGntEAction,SendGntE,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1149_870b_R29_2_I2 /\ RecvGntSAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1149_870b_R29_2_I2 /\ RecvGntEAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv1149_870b_R29_2_I2 /\ StoreAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,StoreAction,Store,Inv1149_870b_R29_2_I2
  \* (Inv1149_870b_R29_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1149_870b_R29_2_I2 /\ SendReqSAction => Inv1149_870b_R29_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1149_870b_R29_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2458_2a15_R21_1_I2
THEOREM L_31 == TypeOK /\ Inv2146_6e63_R28_0_I2 /\ Inv2458_2a15_R21_1_I2 /\ Next => Inv2458_2a15_R21_1_I2'
  <1>. USE A0,A1
  \* (Inv2458_2a15_R21_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ SendReqEAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ RecvReqSAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ RecvReqEAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ SendInvAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ SendInvAckAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ Inv2458_2a15_R21_1_I2 /\ RecvInvAckAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,Inv2146_6e63_R28_0_I2,RecvInvAckAction,RecvInvAck,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ SendGntSAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ SendGntEAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ RecvGntSAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ RecvGntEAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ StoreAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,StoreAction,Store,Inv2458_2a15_R21_1_I2
  \* (Inv2458_2a15_R21_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2458_2a15_R21_1_I2 /\ SendReqSAction => Inv2458_2a15_R21_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2458_2a15_R21_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2146_6e63_R28_0_I2
THEOREM L_32 == TypeOK /\ Inv687_881e_R35_2_I2 /\ Inv50_ba79_R27_1_I1 /\ Inv40_2bf0_R13_1_I1 /\ Safety /\ Inv39_7204_R20_0_I1 /\ Inv2146_6e63_R28_0_I2 /\ Next => Inv2146_6e63_R28_0_I2'
  <1>. USE A0,A1
  \* (Inv2146_6e63_R28_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ SendReqEAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ RecvReqSAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ RecvReqEAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv687_881e_R35_2_I2 /\ Inv2146_6e63_R28_0_I2 /\ SendInvAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,Inv687_881e_R35_2_I2,SendInvAction,SendInv,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv50_ba79_R27_1_I1 /\ Inv40_2bf0_R13_1_I1 /\ Safety /\ Inv2146_6e63_R28_0_I2 /\ SendInvAckAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,Inv50_ba79_R27_1_I1,Inv40_2bf0_R13_1_I1,Safety,SendInvAckAction,SendInvAck,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ RecvInvAckAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ SendGntSAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv39_7204_R20_0_I1 /\ Inv2146_6e63_R28_0_I2 /\ SendGntEAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,Inv39_7204_R20_0_I1,SendGntEAction,SendGntE,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ RecvGntSAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ RecvGntEAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ StoreAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,StoreAction,Store,Inv2146_6e63_R28_0_I2
  \* (Inv2146_6e63_R28_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2146_6e63_R28_0_I2 /\ SendReqSAction => Inv2146_6e63_R28_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2146_6e63_R28_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv40_2bf0_R13_1_I1
THEOREM L_33 == TypeOK /\ Inv4763_b566_R19_0_I2 /\ Inv40_2bf0_R13_1_I1 /\ Next => Inv40_2bf0_R13_1_I1'
  <1>. USE A0,A1
  \* (Inv40_2bf0_R13_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ SendReqEAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ RecvReqSAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ RecvReqEAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv4763_b566_R19_0_I2 /\ Inv40_2bf0_R13_1_I1 /\ SendInvAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,Inv4763_b566_R19_0_I2,SendInvAction,SendInv,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ SendInvAckAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ RecvInvAckAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ SendGntSAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ SendGntEAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ RecvGntSAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ RecvGntEAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ StoreAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,StoreAction,Store,Inv40_2bf0_R13_1_I1
  \* (Inv40_2bf0_R13_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv40_2bf0_R13_1_I1 /\ SendReqSAction => Inv40_2bf0_R13_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv40_2bf0_R13_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4763_b566_R19_0_I2
THEOREM L_34 == TypeOK /\ Inv1103_d53b_R25_0_I4 /\ Inv1103_d53b_R25_0_I4 /\ Inv76_d564_R22_2_I1 /\ Inv4763_b566_R19_0_I2 /\ Next => Inv4763_b566_R19_0_I2'
  <1>. USE A0,A1
  \* (Inv4763_b566_R19_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv4763_b566_R19_0_I2 /\ SendReqEAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ Inv4763_b566_R19_0_I2 /\ RecvReqSAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,Inv1103_d53b_R25_0_I4,RecvReqSAction,RecvReqS,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ Inv4763_b566_R19_0_I2 /\ RecvReqEAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,Inv1103_d53b_R25_0_I4,RecvReqEAction,RecvReqE,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv4763_b566_R19_0_I2 /\ SendInvAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv76_d564_R22_2_I1 /\ Inv4763_b566_R19_0_I2 /\ SendInvAckAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,Inv76_d564_R22_2_I1,SendInvAckAction,SendInvAck,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv4763_b566_R19_0_I2 /\ RecvInvAckAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv4763_b566_R19_0_I2 /\ SendGntSAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv4763_b566_R19_0_I2 /\ SendGntEAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv4763_b566_R19_0_I2 /\ RecvGntSAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv4763_b566_R19_0_I2 /\ RecvGntEAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv4763_b566_R19_0_I2 /\ StoreAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,StoreAction,Store,Inv4763_b566_R19_0_I2
  \* (Inv4763_b566_R19_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv4763_b566_R19_0_I2 /\ SendReqSAction => Inv4763_b566_R19_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv4763_b566_R19_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1103_d53b_R25_0_I4
THEOREM L_35 == TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv957_c432_R31_0_I2 /\ Inv1103_d53b_R25_0_I4 /\ Next => Inv1103_d53b_R25_0_I4'
  <1>. USE A0,A1
  \* (Inv1103_d53b_R25_0_I4,SendReqEAction)
  <1>1. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ SendReqEAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,RecvReqSAction)
  <1>2. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ RecvReqSAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,RecvReqEAction)
  <1>3. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ RecvReqEAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,SendInvAction)
  <1>4. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ SendInvAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,SendInvAction,SendInv,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,SendInvAckAction)
  <1>5. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv1103_d53b_R25_0_I4 /\ SendInvAckAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,Inv1149_870b_R29_2_I2,SendInvAckAction,SendInvAck,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ RecvInvAckAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,SendGntSAction)
  <1>7. TypeOK /\ Inv957_c432_R31_0_I2 /\ Inv1103_d53b_R25_0_I4 /\ SendGntSAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,Inv957_c432_R31_0_I2,SendGntSAction,SendGntS,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,SendGntEAction)
  <1>8. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ SendGntEAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,SendGntEAction,SendGntE,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,RecvGntSAction)
  <1>9. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ RecvGntSAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,RecvGntEAction)
  <1>10. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ RecvGntEAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,StoreAction)
  <1>11. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ StoreAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,StoreAction,Store,Inv1103_d53b_R25_0_I4
  \* (Inv1103_d53b_R25_0_I4,SendReqSAction)
  <1>12. TypeOK /\ Inv1103_d53b_R25_0_I4 /\ SendReqSAction => Inv1103_d53b_R25_0_I4' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1103_d53b_R25_0_I4
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv957_c432_R31_0_I2
THEOREM L_36 == TypeOK /\ Inv26_259c_R15_0_I1 /\ Inv1942_3576_R37_0_I3 /\ Inv957_c432_R31_0_I2 /\ Next => Inv957_c432_R31_0_I2'
  <1>. USE A0,A1
  \* (Inv957_c432_R31_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv957_c432_R31_0_I2 /\ SendReqEAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv957_c432_R31_0_I2 /\ RecvReqSAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv957_c432_R31_0_I2 /\ RecvReqEAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv957_c432_R31_0_I2 /\ SendInvAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv957_c432_R31_0_I2 /\ SendInvAckAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv26_259c_R15_0_I1 /\ Inv1942_3576_R37_0_I3 /\ Inv957_c432_R31_0_I2 /\ RecvInvAckAction => Inv957_c432_R31_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv26_259c_R15_0_I1,
                        Inv1942_3576_R37_0_I3,
                        Inv957_c432_R31_0_I2,
                        TRUE,
                        NEW i \in NODE,
                        RecvInvAck(i),
                        NEW VARI \in NODE'
                 PROVE  ((ExGntd) \/ ((InvSet[VARI] = ShrSet[VARI]) \/ (~(CurCmd = "ReqS"))))'
      BY DEF Inv957_c432_R31_0_I2, RecvInvAckAction
    <2> QED
      BY DEF TypeOK,Inv26_259c_R15_0_I1,Inv1942_3576_R37_0_I3,RecvInvAckAction,RecvInvAck,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv957_c432_R31_0_I2 /\ SendGntSAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv957_c432_R31_0_I2 /\ SendGntEAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv957_c432_R31_0_I2 /\ RecvGntSAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv957_c432_R31_0_I2 /\ RecvGntEAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv957_c432_R31_0_I2 /\ StoreAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,StoreAction,Store,Inv957_c432_R31_0_I2
  \* (Inv957_c432_R31_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv957_c432_R31_0_I2 /\ SendReqSAction => Inv957_c432_R31_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv957_c432_R31_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1942_3576_R37_0_I3
THEOREM L_37 == TypeOK /\ Inv687_881e_R35_2_I2 /\ Inv111_3e57_R40_1_I2 /\ Inv1000_d532_R39_3_I2 /\ Inv848_bea9_R40_1_I2 /\ Inv50_ba79_R27_1_I1 /\ Inv40_2bf0_R13_1_I1 /\ Inv17_9e93_R14_0_I1 /\ Inv1942_3576_R37_0_I3 /\ Next => Inv1942_3576_R37_0_I3'
  <1>. USE A0,A1
  \* (Inv1942_3576_R37_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv1942_3576_R37_0_I3 /\ SendReqEAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv1942_3576_R37_0_I3 /\ RecvReqSAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv1942_3576_R37_0_I3 /\ RecvReqEAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv687_881e_R35_2_I2 /\ Inv1942_3576_R37_0_I3 /\ SendInvAction => Inv1942_3576_R37_0_I3' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv687_881e_R35_2_I2,
                        Inv1942_3576_R37_0_I3,
                        TRUE,
                        NEW i \in NODE,
                        Chan2[i].Cmd = "Empty",
                        InvSet[i] = TRUE,
                        Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"],
                        InvSet' = [InvSet EXCEPT ![i] = FALSE],
                        UNCHANGED <<Cache, Chan1, Chan3, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>,
                        NEW VARI \in NODE',
                        NEW VARJ \in NODE',
                        CurCmd = "ReqE" \/ (CurCmd = "ReqS" /\ ExGntd = TRUE)
                 PROVE  ((Chan3[VARJ].Cmd = "Empty") \/ ((InvSet[VARI] = ShrSet[VARI]) \/ (~(ExGntd) \/ (~(VARI # VARJ)))))'
      BY DEF Inv1942_3576_R37_0_I3, SendInv, SendInvAction
    <2>1. CASE CurCmd = "ReqE"
      BY <2>1 DEF TypeOK,Inv687_881e_R35_2_I2,SendInvAction,SendInv,Inv1942_3576_R37_0_I3
    <2>2. CASE CurCmd = "ReqS" /\ ExGntd = TRUE
      BY <2>2 DEF TypeOK,Inv687_881e_R35_2_I2,SendInvAction,SendInv,Inv1942_3576_R37_0_I3
    <2>3. QED
      BY <2>1, <2>2
  \* (Inv1942_3576_R37_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv111_3e57_R40_1_I2 /\ Inv1000_d532_R39_3_I2 /\ Inv848_bea9_R40_1_I2 /\ Inv50_ba79_R27_1_I1 /\ Inv40_2bf0_R13_1_I1 /\ Inv1942_3576_R37_0_I3 /\ SendInvAckAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,Inv111_3e57_R40_1_I2,Inv1000_d532_R39_3_I2,Inv848_bea9_R40_1_I2,Inv50_ba79_R27_1_I1,Inv40_2bf0_R13_1_I1,SendInvAckAction,SendInvAck,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1942_3576_R37_0_I3 /\ RecvInvAckAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv1942_3576_R37_0_I3 /\ SendGntSAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv17_9e93_R14_0_I1 /\ Inv1942_3576_R37_0_I3 /\ SendGntEAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,Inv17_9e93_R14_0_I1,SendGntEAction,SendGntE,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv1942_3576_R37_0_I3 /\ RecvGntSAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv1942_3576_R37_0_I3 /\ RecvGntEAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv1942_3576_R37_0_I3 /\ StoreAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,StoreAction,Store,Inv1942_3576_R37_0_I3
  \* (Inv1942_3576_R37_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv1942_3576_R37_0_I3 /\ SendReqSAction => Inv1942_3576_R37_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1942_3576_R37_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv111_3e57_R40_1_I2
THEOREM L_38 == TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv1149_870b_R29_2_I2 /\ Inv111_0f39_R7_1_I1 /\ Inv20_5035_R26_0_I1 /\ Inv111_3e57_R40_1_I2 /\ Next => Inv111_3e57_R40_1_I2'
  <1>. USE A0,A1
  \* (Inv111_3e57_R40_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv111_3e57_R40_1_I2 /\ SendReqEAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv111_3e57_R40_1_I2 /\ RecvReqSAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,Inv1149_870b_R29_2_I2,RecvReqSAction,RecvReqS,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv111_3e57_R40_1_I2 /\ RecvReqEAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,Inv1149_870b_R29_2_I2,RecvReqEAction,RecvReqE,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv111_3e57_R40_1_I2 /\ SendInvAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendInvAction,SendInv,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv111_3e57_R40_1_I2 /\ SendInvAckAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv20_5035_R26_0_I1 /\ Inv111_3e57_R40_1_I2 /\ RecvInvAckAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,Inv20_5035_R26_0_I1,RecvInvAckAction,RecvInvAck,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv111_3e57_R40_1_I2 /\ SendGntSAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv111_3e57_R40_1_I2 /\ SendGntEAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv111_3e57_R40_1_I2 /\ RecvGntSAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv111_3e57_R40_1_I2 /\ RecvGntEAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv111_3e57_R40_1_I2 /\ StoreAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,StoreAction,Store,Inv111_3e57_R40_1_I2
  \* (Inv111_3e57_R40_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv111_3e57_R40_1_I2 /\ SendReqSAction => Inv111_3e57_R40_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv111_3e57_R40_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1000_d532_R39_3_I2
THEOREM L_39 == TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv1149_870b_R29_2_I2 /\ Inv23009_51f5_R41_3_I3 /\ Inv111_0f39_R7_1_I1 /\ Inv1000_d532_R39_3_I2 /\ Next => Inv1000_d532_R39_3_I2'
  <1>. USE A0,A1
  \* (Inv1000_d532_R39_3_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1000_d532_R39_3_I2 /\ SendReqEAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv1000_d532_R39_3_I2 /\ RecvReqSAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,Inv1149_870b_R29_2_I2,RecvReqSAction,RecvReqS,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv1149_870b_R29_2_I2 /\ Inv1000_d532_R39_3_I2 /\ RecvReqEAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,Inv1149_870b_R29_2_I2,RecvReqEAction,RecvReqE,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,SendInvAction)
  <1>4. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ Inv1000_d532_R39_3_I2 /\ SendInvAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,Inv23009_51f5_R41_3_I3,SendInvAction,SendInv,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1000_d532_R39_3_I2 /\ SendInvAckAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1000_d532_R39_3_I2 /\ RecvInvAckAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1000_d532_R39_3_I2 /\ SendGntSAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv1000_d532_R39_3_I2 /\ SendGntEAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1000_d532_R39_3_I2 /\ RecvGntSAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1000_d532_R39_3_I2 /\ RecvGntEAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,StoreAction)
  <1>11. TypeOK /\ Inv1000_d532_R39_3_I2 /\ StoreAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,StoreAction,Store,Inv1000_d532_R39_3_I2
  \* (Inv1000_d532_R39_3_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1000_d532_R39_3_I2 /\ SendReqSAction => Inv1000_d532_R39_3_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1000_d532_R39_3_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv23009_51f5_R41_3_I3
THEOREM L_40 == TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ Inv7513_6fbd_R44_0_I3 /\ Inv111_0f39_R7_1_I1 /\ Inv23009_51f5_R41_3_I3 /\ Next => Inv23009_51f5_R41_3_I3'
  <1>. USE A0,A1
  \* (Inv23009_51f5_R41_3_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ SendReqEAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ Inv23009_51f5_R41_3_I3 /\ RecvReqSAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,Inv7513_6fbd_R44_0_I3,RecvReqSAction,RecvReqS,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ Inv23009_51f5_R41_3_I3 /\ RecvReqEAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,Inv7513_6fbd_R44_0_I3,RecvReqEAction,RecvReqE,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,SendInvAction)
  <1>4. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ SendInvAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ SendInvAckAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ RecvInvAckAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ SendGntSAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv23009_51f5_R41_3_I3 /\ SendGntEAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ RecvGntSAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ RecvGntEAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,StoreAction)
  <1>11. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ StoreAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,StoreAction,Store,Inv23009_51f5_R41_3_I3
  \* (Inv23009_51f5_R41_3_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ SendReqSAction => Inv23009_51f5_R41_3_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv23009_51f5_R41_3_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv7513_6fbd_R44_0_I3
THEOREM L_41 == TypeOK /\ Inv23009_51f5_R41_3_I3 /\ Inv111_0f39_R7_1_I1 /\ Inv7513_6fbd_R44_0_I3 /\ Next => Inv7513_6fbd_R44_0_I3'
  <1>. USE A0,A1
  \* (Inv7513_6fbd_R44_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ SendReqEAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ RecvReqSAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ RecvReqEAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv23009_51f5_R41_3_I3 /\ Inv7513_6fbd_R44_0_I3 /\ SendInvAction => Inv7513_6fbd_R44_0_I3' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv23009_51f5_R41_3_I3,
                        Inv7513_6fbd_R44_0_I3,
                        TRUE,
                        NEW i \in NODE,
                        Chan2[i].Cmd = "Empty",
                        InvSet[i] = TRUE,
                        Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"],
                        InvSet' = [InvSet EXCEPT ![i] = FALSE],
                        UNCHANGED <<Cache, Chan1, Chan3, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>,
                        NEW VARI \in NODE',
                        NEW VARJ \in NODE',
                        CurCmd = "ReqE" \/ (CurCmd = "ReqS" /\ ExGntd = TRUE)
                 PROVE  ((InvSet[VARI] = ShrSet[VARI]) \/ (~(ExGntd)) \/ (~(VARI # VARJ)) \/ (~(ShrSet[VARJ])))'
      BY DEF Inv7513_6fbd_R44_0_I3, SendInv, SendInvAction
    <2>1. CASE CurCmd = "ReqE"
      BY <2>1 DEF TypeOK,Inv23009_51f5_R41_3_I3,SendInvAction,SendInv,Inv7513_6fbd_R44_0_I3
    <2>2. CASE CurCmd = "ReqS" /\ ExGntd = TRUE
      BY <2>2 DEF TypeOK,Inv23009_51f5_R41_3_I3,SendInvAction,SendInv,Inv7513_6fbd_R44_0_I3
    <2>3. QED
      BY <2>1, <2>2
  \* (Inv7513_6fbd_R44_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ SendInvAckAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ RecvInvAckAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ SendGntSAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv7513_6fbd_R44_0_I3 /\ SendGntEAction => Inv7513_6fbd_R44_0_I3' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv111_0f39_R7_1_I1,
                        Inv7513_6fbd_R44_0_I3,
                        TRUE,
                        NEW i \in NODE,
                        SendGntE(i),
                        NEW VARI \in NODE',
                        NEW VARJ \in NODE'
                 PROVE  ((InvSet[VARI] = ShrSet[VARI]) \/ (~(ExGntd)) \/ (~(VARI # VARJ)) \/ (~(ShrSet[VARJ])))'
      BY DEF Inv7513_6fbd_R44_0_I3, SendGntEAction
    <2> QED
      BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ RecvGntSAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ RecvGntEAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ StoreAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,StoreAction,Store,Inv7513_6fbd_R44_0_I3
  \* (Inv7513_6fbd_R44_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv7513_6fbd_R44_0_I3 /\ SendReqSAction => Inv7513_6fbd_R44_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv7513_6fbd_R44_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv848_bea9_R40_1_I2
THEOREM L_42 == TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv12_513a_R2_1_I1 /\ Inv9560_0995_R9_0_I2 /\ Inv848_bea9_R40_1_I2 /\ Next => Inv848_bea9_R40_1_I2'
  <1>. USE A0,A1
  \* (Inv848_bea9_R40_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv848_bea9_R40_1_I2 /\ SendReqEAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv848_bea9_R40_1_I2 /\ RecvReqSAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv848_bea9_R40_1_I2 /\ RecvReqEAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv848_bea9_R40_1_I2 /\ SendInvAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv848_bea9_R40_1_I2 /\ SendInvAckAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv848_bea9_R40_1_I2 /\ RecvInvAckAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv848_bea9_R40_1_I2 /\ SendGntSAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,Inv12_513a_R2_1_I1,SendGntSAction,SendGntS,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv848_bea9_R40_1_I2 /\ SendGntEAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,Inv12_513a_R2_1_I1,SendGntEAction,SendGntE,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv848_bea9_R40_1_I2 /\ RecvGntSAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv9560_0995_R9_0_I2 /\ Inv848_bea9_R40_1_I2 /\ RecvGntEAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,Inv9560_0995_R9_0_I2,RecvGntEAction,RecvGntE,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv848_bea9_R40_1_I2 /\ StoreAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,StoreAction,Store,Inv848_bea9_R40_1_I2
  \* (Inv848_bea9_R40_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv848_bea9_R40_1_I2 /\ SendReqSAction => Inv848_bea9_R40_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv848_bea9_R40_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv12_513a_R2_1_I1
THEOREM L_43 == TypeOK /\ Inv7_7199_R6_1_I1 /\ Inv5_a2c7_R3_1_I1 /\ Inv12_513a_R2_1_I1 /\ Next => Inv12_513a_R2_1_I1'
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


\*** Inv687_881e_R35_2_I2
THEOREM L_44 == TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv4043_dbee_R22_0_I2 /\ Inv1000_d532_R39_3_I2 /\ Inv111_0f39_R7_1_I1 /\ Inv687_881e_R35_2_I2 /\ Next => Inv687_881e_R35_2_I2'
  <1>. USE A0,A1
  \* (Inv687_881e_R35_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv687_881e_R35_2_I2 /\ SendReqEAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv687_881e_R35_2_I2 /\ RecvReqSAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,Inv4043_dbee_R22_0_I2,RecvReqSAction,RecvReqS,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv4043_dbee_R22_0_I2 /\ Inv687_881e_R35_2_I2 /\ RecvReqEAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,Inv4043_dbee_R22_0_I2,RecvReqEAction,RecvReqE,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv687_881e_R35_2_I2 /\ SendInvAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1000_d532_R39_3_I2 /\ Inv687_881e_R35_2_I2 /\ SendInvAckAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,Inv1000_d532_R39_3_I2,SendInvAckAction,SendInvAck,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv687_881e_R35_2_I2 /\ RecvInvAckAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv687_881e_R35_2_I2 /\ SendGntSAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv111_0f39_R7_1_I1 /\ Inv687_881e_R35_2_I2 /\ SendGntEAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,Inv111_0f39_R7_1_I1,SendGntEAction,SendGntE,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv687_881e_R35_2_I2 /\ RecvGntSAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv687_881e_R35_2_I2 /\ RecvGntEAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv687_881e_R35_2_I2 /\ StoreAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,StoreAction,Store,Inv687_881e_R35_2_I2
  \* (Inv687_881e_R35_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv687_881e_R35_2_I2 /\ SendReqSAction => Inv687_881e_R35_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv687_881e_R35_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv33_1336_R1_1_I1
THEOREM L_45 == TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv33_1336_R1_1_I1 /\ Next => Inv33_1336_R1_1_I1'
  <1>. USE A0,A1
  \* (Inv33_1336_R1_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv33_1336_R1_1_I1 /\ SendReqEAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv33_1336_R1_1_I1 /\ RecvReqSAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv33_1336_R1_1_I1 /\ RecvReqEAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv33_1336_R1_1_I1 /\ SendInvAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv33_1336_R1_1_I1 /\ SendInvAckAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv33_1336_R1_1_I1 /\ RecvInvAckAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv5_a2c7_R3_1_I1 /\ Inv33_1336_R1_1_I1 /\ SendGntSAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,Inv5_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv33_1336_R1_1_I1 /\ SendGntEAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv33_1336_R1_1_I1 /\ RecvGntSAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv33_1336_R1_1_I1 /\ RecvGntEAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv33_1336_R1_1_I1 /\ StoreAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,StoreAction,Store,Inv33_1336_R1_1_I1
  \* (Inv33_1336_R1_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv33_1336_R1_1_I1 /\ SendReqSAction => Inv33_1336_R1_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv33_1336_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_3662_R0_1_I1
THEOREM L_46 == TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv33_1336_R1_1_I1 /\ Inv11_3662_R0_1_I1 /\ Next => Inv11_3662_R0_1_I1'
  <1>. USE A0,A1
  \* (Inv11_3662_R0_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv11_3662_R0_1_I1 /\ SendReqEAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv11_3662_R0_1_I1 /\ RecvReqSAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv11_3662_R0_1_I1 /\ RecvReqEAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv11_3662_R0_1_I1 /\ SendInvAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_3662_R0_1_I1 /\ SendInvAckAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv11_3662_R0_1_I1 /\ RecvInvAckAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv12_513a_R2_1_I1 /\ Inv11_3662_R0_1_I1 /\ SendGntSAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,Inv12_513a_R2_1_I1,SendGntSAction,SendGntS,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv11_3662_R0_1_I1 /\ SendGntEAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_3662_R0_1_I1 /\ RecvGntSAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv33_1336_R1_1_I1 /\ Inv11_3662_R0_1_I1 /\ RecvGntEAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,Inv33_1336_R1_1_I1,RecvGntEAction,RecvGntE,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv11_3662_R0_1_I1 /\ StoreAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,StoreAction,Store,Inv11_3662_R0_1_I1
  \* (Inv11_3662_R0_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv11_3662_R0_1_I1 /\ SendReqSAction => Inv11_3662_R0_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv11_3662_R0_1_I1
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
    <1>3. Init => Inv5378_0d22_R1_0_I2 BY DEF Init, Inv5378_0d22_R1_0_I2, IndGlobal
    <1>4. Init => Inv1_85ad_R3_0_I1 BY DEF Init, Inv1_85ad_R3_0_I1, IndGlobal
    <1>5. Init => Inv1_eb94_R7_0_I1 BY DEF Init, Inv1_eb94_R7_0_I1, IndGlobal
    <1>6. Init => Inv17_9e93_R14_0_I1 BY DEF Init, Inv17_9e93_R14_0_I1, IndGlobal
    <1>7. Init => Inv39_7204_R20_0_I1 BY DEF Init, Inv39_7204_R20_0_I1, IndGlobal
    <1>8. Init => Inv20_5035_R26_0_I1 BY DEF Init, Inv20_5035_R26_0_I1, IndGlobal
    <1>9. Init => Inv13_45c1_R14_2_I1 BY DEF Init, Inv13_45c1_R14_2_I1, IndGlobal
    <1>10. Init => Inv4043_dbee_R22_0_I2 BY DEF Init, Inv4043_dbee_R22_0_I2, IndGlobal
    <1>11. Init => Inv4424_0201_R14_1_I2 BY DEF Init, Inv4424_0201_R14_1_I2, IndGlobal
    <1>12. Init => Inv1057_089e_R21_0_I3 BY DEF Init, Inv1057_089e_R21_0_I3, IndGlobal
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
    <1>24. Init => Inv6410_fc2f_R3_2_I2 BY DEF Init, Inv6410_fc2f_R3_2_I2, IndGlobal
    <1>25. Init => Inv9560_0995_R9_0_I2 BY DEF Init, Inv9560_0995_R9_0_I2, IndGlobal
    <1>26. Init => Inv5_a2c7_R3_1_I1 BY DEF Init, Inv5_a2c7_R3_1_I1, IndGlobal
    <1>27. Init => Inv111_0f39_R7_1_I1 BY DEF Init, Inv111_0f39_R7_1_I1, IndGlobal
    <1>28. Init => Inv26_259c_R15_0_I1 BY DEF Init, Inv26_259c_R15_0_I1, IndGlobal
    <1>29. Init => Inv76_d564_R22_2_I1 BY DEF Init, Inv76_d564_R22_2_I1, IndGlobal
    <1>30. Init => Inv1149_870b_R29_2_I2 BY DEF Init, Inv1149_870b_R29_2_I2, IndGlobal
    <1>31. Init => Inv2458_2a15_R21_1_I2 BY DEF Init, Inv2458_2a15_R21_1_I2, IndGlobal
    <1>32. Init => Inv2146_6e63_R28_0_I2 BY DEF Init, Inv2146_6e63_R28_0_I2, IndGlobal
    <1>33. Init => Inv40_2bf0_R13_1_I1 BY DEF Init, Inv40_2bf0_R13_1_I1, IndGlobal
    <1>34. Init => Inv4763_b566_R19_0_I2 BY DEF Init, Inv4763_b566_R19_0_I2, IndGlobal
    <1>35. Init => Inv1103_d53b_R25_0_I4 BY DEF Init, Inv1103_d53b_R25_0_I4, IndGlobal
    <1>36. Init => Inv957_c432_R31_0_I2 BY DEF Init, Inv957_c432_R31_0_I2, IndGlobal
    <1>37. Init => Inv1942_3576_R37_0_I3 BY DEF Init, Inv1942_3576_R37_0_I3, IndGlobal
    <1>38. Init => Inv111_3e57_R40_1_I2 BY DEF Init, Inv111_3e57_R40_1_I2, IndGlobal
    <1>39. Init => Inv1000_d532_R39_3_I2 BY DEF Init, Inv1000_d532_R39_3_I2, IndGlobal
    <1>40. Init => Inv23009_51f5_R41_3_I3 BY DEF Init, Inv23009_51f5_R41_3_I3, IndGlobal
    <1>41. Init => Inv7513_6fbd_R44_0_I3 BY DEF Init, Inv7513_6fbd_R44_0_I3, IndGlobal
    <1>42. Init => Inv848_bea9_R40_1_I2 BY DEF Init, Inv848_bea9_R40_1_I2, IndGlobal
    <1>43. Init => Inv12_513a_R2_1_I1 BY DEF Init, Inv12_513a_R2_1_I1, IndGlobal
    <1>44. Init => Inv687_881e_R35_2_I2 BY DEF Init, Inv687_881e_R35_2_I2, IndGlobal
    <1>45. Init => Inv33_1336_R1_1_I1 BY DEF Init, Inv33_1336_R1_1_I1, IndGlobal
    <1>46. Init => Inv11_3662_R0_1_I1 BY DEF Init, Inv11_3662_R0_1_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36,<1>37,<1>38,<1>39,<1>40,<1>41,<1>42,<1>43,<1>44,<1>45,<1>46 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36,L_37,L_38,L_39,L_40,L_41,L_42,L_43,L_44,L_45,L_46 DEF Next, IndGlobal

====