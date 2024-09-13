------------------------- MODULE GermanCache_IndProofs -------------------------
EXTENDS GermanCache

\* Proof Graph Stats
\* ==================
\* seed: 7
\* num proof graph nodes: 44
\* num proof obligations: 528
Safety == CtrlProp1
Inv104_03a2_R0_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Cache[VARJ].State = "I") \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv3990_3a8e_R0_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARI].Cmd = "Empty") \/ (~(Cache[VARJ].State = "E") \/ (~(VARI # VARJ)))
Inv1011_61c6_R1_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Empty") \/ (~(Chan2[VARI].Cmd = "GntE") \/ (~(VARI # VARJ)))
Inv16_d756_R1_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((ShrSet[VARI]))
Inv11_513a_R2_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Cache[VARI].State = "E"))
Inv2613_6920_R2_3_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))
Inv1_85ad_R3_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
Inv4_a2c7_R3_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Chan2[VARI].Cmd = "GntE"))
Inv3533_fc2f_R3_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))
Inv10_8267_R4_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((Chan3[VARI].Cmd = "Empty"))
Inv7_7199_R5_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Cache[VARJ].State = "E"))
Inv8303_b7f8_R6_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(ShrSet[VARJ]) \/ (~(VARI # VARJ)))
Inv1_eb94_R7_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((Chan3[VARI].Cmd = "Empty"))
Inv10_84e4_R7_1_I1 == \A VARJ \in NODE : (ShrSet[VARJ]) \/ (~(InvSet[VARJ]))
Inv13_5b11_R8_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "GntE"))
Inv4026_ce35_R9_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(ShrSet[VARJ]) \/ (~(VARI # VARJ)))
Inv29_0f39_R9_2_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(InvSet[VARI]))
Inv11_c03f_R10_0_I1 == \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Empty") \/ ((Chan3[VARJ].Cmd = "Empty"))
Inv13_9e93_R13_0_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
Inv2801_c9e4_R13_1_I2 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((CurCmd = "ReqE") \/ ((ExGntd)))
Inv12_45c1_R13_2_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(InvSet[VARI]))
Inv10_259c_R14_0_I1 == \A VARJ \in NODE : (Chan3[VARJ].Cmd = "Empty") \/ (~(InvSet[VARJ]))
Inv55_c47d_R15_1_I1 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(Chan2[VARJ].Cmd = "Inv"))
Inv37_7204_R19_0_I1 == \A VARI \in NODE : (ShrSet[VARI]) \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv1051_a1d6_R20_0_I3 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd)) \/ ((Chan3[VARJ].Cmd = "Empty")) \/ (~(VARI # VARJ))
Inv2426_1275_R20_1_I2 == \A VARI \in NODE : (CurCmd = "ReqE") \/ ((ExGntd) \/ (~(Chan2[VARI].Cmd = "Inv")))
Inv2088_575b_R21_0_I2 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ ((CurCmd = "ReqE") \/ ((CurCmd = "ReqS")))
Inv64_d564_R21_2_I1 == \A VARI \in NODE : ~(Chan2[VARI].Cmd = "Inv") \/ (~(InvSet[VARI]))
Inv18_5035_R24_0_I1 == \A VARI \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv4944_1b30_R25_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "Inv") \/ (~(ExGntd)))
Inv342_1d58_R27_2_I2 == \A VARI \in NODE : (CurCmd = "ReqE") \/ ((CurCmd = "ReqS") \/ (~(Chan2[VARI].Cmd = "Inv")))
Inv25_6e21_R30_1_I2 == \A VARI \in NODE : (Cache[VARI].State = "E") \/ (~(ExGntd)) \/ (~(Chan2[VARI].Cmd = "Inv"))
Inv1031_515a_R30_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan3[VARJ].Cmd = "Empty") \/ (~(ExGntd)) \/ (~(InvSet[VARI]))
Inv24_ba79_R32_1_I2 == \A VARI \in NODE : ~(Cache[VARI].State = "S") \/ (~(ExGntd))
Inv580_b566_R32_1_I2 == \A VARI \in NODE : ~(Cache[VARI].State = "I") \/ (~(Chan2[VARI].Cmd = "Empty") \/ (~(InvSet[VARI])))
Inv1290_ee95_R33_3_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "Inv") \/ (~(ExGntd) \/ (~(InvSet[VARJ])))
Inv2275_b1ee_R34_0_I3 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((Chan2[VARI].Cmd = "GntE") \/ (~(ExGntd)) \/ ((Chan2[VARI].Cmd = "Inv")))
Inv2351_aaa7_R35_0_I4 == \A VARI \in NODE : \A VARJ \in NODE : (CurCmd = "ReqE") \/ ((CurCmd = "ReqS") \/ (~(Chan2[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "Empty")))) \/ (~(ShrSet[VARJ])) \/ (~(Cache[VARJ].State = "I"))
Inv3928_4fdf_R36_3_I3 == \A VARI \in NODE : \A VARJ \in NODE : ~(ExGntd) \/ (~(InvSet[VARI]) \/ (~(VARI # VARJ))) \/ (~(InvSet[VARJ]))
Inv3402_aace_R38_0_I4 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARI].Cmd = "Inv") \/ ((CurCmd = "ReqE") \/ (~(Cache[VARJ].State = "I") \/ (~(ShrSet[VARJ]))) \/ ((ExGntd))) \/ (~(Chan2[VARJ].Cmd = "Empty"))
Inv8711_7c56_R39_0_I3 == \A VARI \in NODE : \A VARJ \in NODE : ~(ExGntd) \/ (~(ShrSet[VARI]) \/ (~(VARI # VARJ))) \/ (~(ShrSet[VARJ]))
Inv3085_f335_R40_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Empty") \/ ((Chan3[VARI].Cmd = "Empty") \/ (~(ExGntd)))
Inv10_59dd_R42_1_I2 == \A VARI \in NODE : (Cache[VARI].State = "E") \/ (~(Chan2[VARI].Cmd = "Inv") \/ (~(ExGntd)))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv104_03a2_R0_0_I1
  /\ Inv1011_61c6_R1_0_I2
  /\ Inv1_85ad_R3_0_I1
  /\ Inv1_eb94_R7_0_I1
  /\ Inv13_9e93_R13_0_I1
  /\ Inv37_7204_R19_0_I1
  /\ Inv18_5035_R24_0_I1
  /\ Inv12_45c1_R13_2_I1
  /\ Inv2088_575b_R21_0_I2
  /\ Inv2801_c9e4_R13_1_I2
  /\ Inv1051_a1d6_R20_0_I3
  /\ Inv4944_1b30_R25_1_I2
  /\ Inv25_6e21_R30_1_I2
  /\ Inv24_ba79_R32_1_I2
  /\ Inv2275_b1ee_R34_0_I3
  /\ Inv16_d756_R1_2_I1
  /\ Inv10_8267_R4_2_I1
  /\ Inv11_c03f_R10_0_I1
  /\ Inv580_b566_R32_1_I2
  /\ Inv2351_aaa7_R35_0_I4
  /\ Inv3402_aace_R38_0_I4
  /\ Inv3085_f335_R40_0_I2
  /\ Inv3990_3a8e_R0_1_I2
  /\ Inv11_513a_R2_1_I1
  /\ Inv4_a2c7_R3_1_I1
  /\ Inv13_5b11_R8_0_I1
  /\ Inv55_c47d_R15_1_I1
  /\ Inv3533_fc2f_R3_2_I2
  /\ Inv4026_ce35_R9_0_I2
  /\ Inv29_0f39_R9_2_I1
  /\ Inv7_7199_R5_1_I1
  /\ Inv2613_6920_R2_3_I2
  /\ Inv8303_b7f8_R6_1_I2
  /\ Inv10_59dd_R42_1_I2
  /\ Inv1031_515a_R30_2_I2
  /\ Inv1290_ee95_R33_3_I2
  /\ Inv342_1d58_R27_2_I2
  /\ Inv2426_1275_R20_1_I2
  /\ Inv3928_4fdf_R36_3_I3
  /\ Inv8711_7c56_R39_0_I3
  /\ Inv64_d564_R21_2_I1
  /\ Inv10_84e4_R7_1_I1
  /\ Inv10_259c_R14_0_I1


\* mean in-degree: 2.477272727272727
\* median in-degree: 2
\* max in-degree: 5
\* min in-degree: 0
\* mean variable slice size: 0

USE DEF CtrlProp1
ASSUME A1 == \E N \in Nat : NODE = 1..N /\ IsFiniteSet(NODE) /\ NODE # {}
ASSUME A2 == \E N \in Nat : DATA = 1..N /\ IsFiniteSet(DATA) /\ DATA # {}

USE A1,A2


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,SendReqEAction)
  <1> USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE
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
THEOREM L_1 == TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ Inv104_03a2_R0_0_I1 /\ Safety /\ Next => Safety'
  \* (Safety,SendReqEAction)
  <1>1. TypeOK /\ Safety /\ SendReqEAction => Safety' BY DEF TypeOK,SendReqEAction,SendReqE,Safety
  \* (Safety,RecvReqSAction)
  <1>2. TypeOK /\ Safety /\ RecvReqSAction => Safety' BY DEF TypeOK,RecvReqSAction,RecvReqS,Safety
  \* (Safety,RecvReqEAction)
  <1>3. TypeOK /\ Safety /\ RecvReqEAction => Safety' BY DEF TypeOK,RecvReqEAction,RecvReqE,Safety
  \* (Safety,SendInvAction)
  <1>4. TypeOK /\ Safety /\ SendInvAction => Safety' BY DEF TypeOK,SendInvAction,SendInv,Safety
  \* (Safety,SendInvAckAction)
  <1>5. TypeOK /\ Safety /\ SendInvAckAction => Safety' BY DEF TypeOK,SendInvAckAction,SendInvAck,Safety
  \* (Safety,RecvInvAckAction)
  <1>6. TypeOK /\ Safety /\ RecvInvAckAction => Safety' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Safety
  \* (Safety,SendGntSAction)
  <1>7. TypeOK /\ Safety /\ SendGntSAction => Safety' BY DEF TypeOK,SendGntSAction,SendGntS,Safety
  \* (Safety,SendGntEAction)
  <1>8. TypeOK /\ Safety /\ SendGntEAction => Safety' BY DEF TypeOK,SendGntEAction,SendGntE,Safety
  \* (Safety,RecvGntSAction)
  <1>9. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ Safety /\ RecvGntSAction => Safety' BY DEF TypeOK,Inv3990_3a8e_R0_1_I2,RecvGntSAction,RecvGntS,Safety
  \* (Safety,RecvGntEAction)
  <1>10. TypeOK /\ Inv104_03a2_R0_0_I1 /\ Safety /\ RecvGntEAction => Safety' BY DEF TypeOK,Inv104_03a2_R0_0_I1,RecvGntEAction,RecvGntE,Safety
  \* (Safety,StoreAction)
  <1>11. TypeOK /\ Safety /\ StoreAction => Safety' BY DEF TypeOK,StoreAction,Store,Safety
  \* (Safety,SendReqSAction)
  <1>12. TypeOK /\ Safety /\ SendReqSAction => Safety' BY DEF TypeOK,SendReqSAction,SendReqS,Safety
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv104_03a2_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv16_d756_R1_2_I1 /\ Inv1011_61c6_R1_0_I2 /\ Inv1011_61c6_R1_0_I2 /\ Inv104_03a2_R0_0_I1 /\ Next => Inv104_03a2_R0_0_I1'
  \* (Inv104_03a2_R0_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv104_03a2_R0_0_I1 /\ SendReqEAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv104_03a2_R0_0_I1 /\ RecvReqSAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv104_03a2_R0_0_I1 /\ RecvReqEAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv104_03a2_R0_0_I1 /\ SendInvAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv104_03a2_R0_0_I1 /\ SendInvAckAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv104_03a2_R0_0_I1 /\ RecvInvAckAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv104_03a2_R0_0_I1 /\ SendGntSAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv16_d756_R1_2_I1 /\ Inv104_03a2_R0_0_I1 /\ SendGntEAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,Inv16_d756_R1_2_I1,SendGntEAction,SendGntE,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ Inv104_03a2_R0_0_I1 /\ RecvGntSAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,Inv1011_61c6_R1_0_I2,RecvGntSAction,RecvGntS,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ Inv104_03a2_R0_0_I1 /\ RecvGntEAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,Inv1011_61c6_R1_0_I2,RecvGntEAction,RecvGntE,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv104_03a2_R0_0_I1 /\ StoreAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,StoreAction,Store,Inv104_03a2_R0_0_I1
  \* (Inv104_03a2_R0_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv104_03a2_R0_0_I1 /\ SendReqSAction => Inv104_03a2_R0_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv104_03a2_R0_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1011_61c6_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ Inv4_a2c7_R3_1_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv1011_61c6_R1_0_I2 /\ Next => Inv1011_61c6_R1_0_I2'
  \* (Inv1011_61c6_R1_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ SendReqEAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ RecvReqSAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ RecvReqEAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ Inv1011_61c6_R1_0_I2 /\ SendInvAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,Inv3533_fc2f_R3_2_I2,SendInvAction,SendInv,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ SendInvAckAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ RecvInvAckAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ Inv1011_61c6_R1_0_I2 /\ SendGntSAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,Inv4_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv1011_61c6_R1_0_I2 /\ SendGntEAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ RecvGntSAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ RecvGntEAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ StoreAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,StoreAction,Store,Inv1011_61c6_R1_0_I2
  \* (Inv1011_61c6_R1_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ SendReqSAction => Inv1011_61c6_R1_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1011_61c6_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_85ad_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv10_84e4_R7_1_I1 /\ Inv1_eb94_R7_0_I1 /\ Inv1_85ad_R3_0_I1 /\ Next => Inv1_85ad_R3_0_I1'
  \* (Inv1_85ad_R3_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv1_85ad_R3_0_I1 /\ SendReqEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvReqSAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv1_85ad_R3_0_I1 /\ RecvReqEAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1_85ad_R3_0_I1
  \* (Inv1_85ad_R3_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_84e4_R7_1_I1 /\ Inv1_85ad_R3_0_I1 /\ SendInvAction => Inv1_85ad_R3_0_I1' BY DEF TypeOK,Inv10_84e4_R7_1_I1,SendInvAction,SendInv,Inv1_85ad_R3_0_I1
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
THEOREM L_5 == TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv2801_c9e4_R13_1_I2 /\ Inv13_9e93_R13_0_I1 /\ Inv1_eb94_R7_0_I1 /\ Next => Inv1_eb94_R7_0_I1'
  \* (Inv1_eb94_R7_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendReqEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvReqSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvReqEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv1_eb94_R7_0_I1 /\ SendInvAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv12_45c1_R13_2_I1,SendInvAction,SendInv,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendInvAckAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvInvAckAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ Inv1_eb94_R7_0_I1 /\ SendGntSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv2801_c9e4_R13_1_I2,SendGntSAction,SendGntS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ Inv1_eb94_R7_0_I1 /\ SendGntEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,Inv13_9e93_R13_0_I1,SendGntEAction,SendGntE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvGntSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv1_eb94_R7_0_I1 /\ RecvGntEAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv1_eb94_R7_0_I1 /\ StoreAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,StoreAction,Store,Inv1_eb94_R7_0_I1
  \* (Inv1_eb94_R7_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv1_eb94_R7_0_I1 /\ SendReqSAction => Inv1_eb94_R7_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1_eb94_R7_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv13_9e93_R13_0_I1
THEOREM L_6 == TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv13_9e93_R13_0_I1 /\ Next => Inv13_9e93_R13_0_I1'
  \* (Inv13_9e93_R13_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv13_9e93_R13_0_I1 /\ SendReqEAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv13_9e93_R13_0_I1 /\ RecvReqSAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv13_9e93_R13_0_I1 /\ RecvReqEAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_9e93_R13_0_I1 /\ SendInvAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv13_9e93_R13_0_I1 /\ SendInvAckAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,Inv37_7204_R19_0_I1,SendInvAckAction,SendInvAck,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv13_9e93_R13_0_I1 /\ RecvInvAckAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv13_9e93_R13_0_I1 /\ SendGntSAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ SendGntEAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv13_9e93_R13_0_I1 /\ RecvGntSAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv13_9e93_R13_0_I1 /\ RecvGntEAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv13_9e93_R13_0_I1 /\ StoreAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,StoreAction,Store,Inv13_9e93_R13_0_I1
  \* (Inv13_9e93_R13_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv13_9e93_R13_0_I1 /\ SendReqSAction => Inv13_9e93_R13_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv13_9e93_R13_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv37_7204_R19_0_I1
THEOREM L_7 == TypeOK /\ Inv10_84e4_R7_1_I1 /\ Inv18_5035_R24_0_I1 /\ Inv37_7204_R19_0_I1 /\ Next => Inv37_7204_R19_0_I1'
  \* (Inv37_7204_R19_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv37_7204_R19_0_I1 /\ SendReqEAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv37_7204_R19_0_I1 /\ RecvReqSAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv37_7204_R19_0_I1 /\ RecvReqEAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_84e4_R7_1_I1 /\ Inv37_7204_R19_0_I1 /\ SendInvAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,Inv10_84e4_R7_1_I1,SendInvAction,SendInv,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv37_7204_R19_0_I1 /\ SendInvAckAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv18_5035_R24_0_I1 /\ Inv37_7204_R19_0_I1 /\ RecvInvAckAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,Inv18_5035_R24_0_I1,RecvInvAckAction,RecvInvAck,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv37_7204_R19_0_I1 /\ SendGntSAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv37_7204_R19_0_I1 /\ SendGntEAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv37_7204_R19_0_I1 /\ RecvGntSAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv37_7204_R19_0_I1 /\ RecvGntEAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv37_7204_R19_0_I1 /\ StoreAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,StoreAction,Store,Inv37_7204_R19_0_I1
  \* (Inv37_7204_R19_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv37_7204_R19_0_I1 /\ SendReqSAction => Inv37_7204_R19_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv37_7204_R19_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv18_5035_R24_0_I1
THEOREM L_8 == TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv18_5035_R24_0_I1 /\ Next => Inv18_5035_R24_0_I1'
  \* (Inv18_5035_R24_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv18_5035_R24_0_I1 /\ SendReqEAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv18_5035_R24_0_I1 /\ RecvReqSAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv18_5035_R24_0_I1 /\ RecvReqEAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv18_5035_R24_0_I1 /\ SendInvAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,Inv12_45c1_R13_2_I1,SendInvAction,SendInv,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv18_5035_R24_0_I1 /\ SendInvAckAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv18_5035_R24_0_I1 /\ RecvInvAckAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv18_5035_R24_0_I1 /\ SendGntSAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv18_5035_R24_0_I1 /\ SendGntEAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv18_5035_R24_0_I1 /\ RecvGntSAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv18_5035_R24_0_I1 /\ RecvGntEAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv18_5035_R24_0_I1 /\ StoreAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,StoreAction,Store,Inv18_5035_R24_0_I1
  \* (Inv18_5035_R24_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv18_5035_R24_0_I1 /\ SendReqSAction => Inv18_5035_R24_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv18_5035_R24_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv12_45c1_R13_2_I1
THEOREM L_9 == TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv2088_575b_R21_0_I2 /\ Inv64_d564_R21_2_I1 /\ Inv12_45c1_R13_2_I1 /\ Next => Inv12_45c1_R13_2_I1'
  \* (Inv12_45c1_R13_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv12_45c1_R13_2_I1 /\ SendReqEAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv12_45c1_R13_2_I1 /\ RecvReqSAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,Inv2088_575b_R21_0_I2,RecvReqSAction,RecvReqS,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv12_45c1_R13_2_I1 /\ RecvReqEAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,Inv2088_575b_R21_0_I2,RecvReqEAction,RecvReqE,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv12_45c1_R13_2_I1 /\ SendInvAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv64_d564_R21_2_I1 /\ Inv12_45c1_R13_2_I1 /\ SendInvAckAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,Inv64_d564_R21_2_I1,SendInvAckAction,SendInvAck,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv12_45c1_R13_2_I1 /\ RecvInvAckAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv12_45c1_R13_2_I1 /\ SendGntSAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv12_45c1_R13_2_I1 /\ SendGntEAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv12_45c1_R13_2_I1 /\ RecvGntSAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv12_45c1_R13_2_I1 /\ RecvGntEAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv12_45c1_R13_2_I1 /\ StoreAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,StoreAction,Store,Inv12_45c1_R13_2_I1
  \* (Inv12_45c1_R13_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv12_45c1_R13_2_I1 /\ SendReqSAction => Inv12_45c1_R13_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv12_45c1_R13_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2088_575b_R21_0_I2
THEOREM L_10 == TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv2801_c9e4_R13_1_I2 /\ Inv13_9e93_R13_0_I1 /\ Inv2088_575b_R21_0_I2 /\ Next => Inv2088_575b_R21_0_I2'
  \* (Inv2088_575b_R21_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2088_575b_R21_0_I2 /\ SendReqEAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2088_575b_R21_0_I2 /\ RecvReqSAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2088_575b_R21_0_I2 /\ RecvReqEAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2088_575b_R21_0_I2 /\ SendInvAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv2088_575b_R21_0_I2 /\ SendInvAckAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,Inv342_1d58_R27_2_I2,SendInvAckAction,SendInvAck,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2088_575b_R21_0_I2 /\ RecvInvAckAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ Inv2088_575b_R21_0_I2 /\ SendGntSAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,Inv2801_c9e4_R13_1_I2,SendGntSAction,SendGntS,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ Inv2088_575b_R21_0_I2 /\ SendGntEAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,Inv13_9e93_R13_0_I1,SendGntEAction,SendGntE,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2088_575b_R21_0_I2 /\ RecvGntSAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv2088_575b_R21_0_I2 /\ RecvGntEAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv2088_575b_R21_0_I2 /\ StoreAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,StoreAction,Store,Inv2088_575b_R21_0_I2
  \* (Inv2088_575b_R21_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2088_575b_R21_0_I2 /\ SendReqSAction => Inv2088_575b_R21_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2088_575b_R21_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2801_c9e4_R13_1_I2
THEOREM L_11 == TypeOK /\ Inv2426_1275_R20_1_I2 /\ Inv1051_a1d6_R20_0_I3 /\ Inv2801_c9e4_R13_1_I2 /\ Next => Inv2801_c9e4_R13_1_I2'
  \* (Inv2801_c9e4_R13_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ SendReqEAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ RecvReqSAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ RecvReqEAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ SendInvAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv2426_1275_R20_1_I2 /\ Inv2801_c9e4_R13_1_I2 /\ SendInvAckAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,Inv2426_1275_R20_1_I2,SendInvAckAction,SendInvAck,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ Inv2801_c9e4_R13_1_I2 /\ RecvInvAckAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,Inv1051_a1d6_R20_0_I3,RecvInvAckAction,RecvInvAck,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ SendGntSAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ SendGntEAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ RecvGntSAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ RecvGntEAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ StoreAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,StoreAction,Store,Inv2801_c9e4_R13_1_I2
  \* (Inv2801_c9e4_R13_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ SendReqSAction => Inv2801_c9e4_R13_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2801_c9e4_R13_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1051_a1d6_R20_0_I3
THEOREM L_12 == TypeOK /\ Inv4944_1b30_R25_1_I2 /\ Inv13_9e93_R13_0_I1 /\ Inv1051_a1d6_R20_0_I3 /\ Next => Inv1051_a1d6_R20_0_I3'
  \* (Inv1051_a1d6_R20_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ SendReqEAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ RecvReqSAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ RecvReqEAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ SendInvAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ Inv1051_a1d6_R20_0_I3 /\ SendInvAckAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,Inv4944_1b30_R25_1_I2,SendInvAckAction,SendInvAck,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ RecvInvAckAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ SendGntSAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ Inv1051_a1d6_R20_0_I3 /\ SendGntEAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,Inv13_9e93_R13_0_I1,SendGntEAction,SendGntE,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ RecvGntSAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ RecvGntEAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ StoreAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,StoreAction,Store,Inv1051_a1d6_R20_0_I3
  \* (Inv1051_a1d6_R20_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv1051_a1d6_R20_0_I3 /\ SendReqSAction => Inv1051_a1d6_R20_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1051_a1d6_R20_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4944_1b30_R25_1_I2
THEOREM L_13 == TypeOK /\ Inv1031_515a_R30_2_I2 /\ Inv25_6e21_R30_1_I2 /\ Inv3990_3a8e_R0_1_I2 /\ Inv37_7204_R19_0_I1 /\ Inv4944_1b30_R25_1_I2 /\ Next => Inv4944_1b30_R25_1_I2'
  \* (Inv4944_1b30_R25_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ SendReqEAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ RecvReqSAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ RecvReqEAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1031_515a_R30_2_I2 /\ Inv4944_1b30_R25_1_I2 /\ SendInvAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,Inv1031_515a_R30_2_I2,SendInvAction,SendInv,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv25_6e21_R30_1_I2 /\ Inv3990_3a8e_R0_1_I2 /\ Inv4944_1b30_R25_1_I2 /\ SendInvAckAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,Inv25_6e21_R30_1_I2,Inv3990_3a8e_R0_1_I2,SendInvAckAction,SendInvAck,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ RecvInvAckAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ SendGntSAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv4944_1b30_R25_1_I2 /\ SendGntEAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,Inv37_7204_R19_0_I1,SendGntEAction,SendGntE,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ RecvGntSAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ RecvGntEAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ StoreAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,StoreAction,Store,Inv4944_1b30_R25_1_I2
  \* (Inv4944_1b30_R25_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ SendReqSAction => Inv4944_1b30_R25_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv4944_1b30_R25_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv25_6e21_R30_1_I2
THEOREM L_14 == TypeOK /\ Inv24_ba79_R32_1_I2 /\ Inv580_b566_R32_1_I2 /\ Inv37_7204_R19_0_I1 /\ Inv25_6e21_R30_1_I2 /\ Next => Inv25_6e21_R30_1_I2'
  <1> USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE
  \* (Inv25_6e21_R30_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv25_6e21_R30_1_I2 /\ SendReqEAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv25_6e21_R30_1_I2 /\ RecvReqSAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv25_6e21_R30_1_I2 /\ RecvReqEAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv24_ba79_R32_1_I2 /\ Inv580_b566_R32_1_I2 /\ Inv25_6e21_R30_1_I2 /\ SendInvAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,Inv24_ba79_R32_1_I2,Inv580_b566_R32_1_I2,SendInvAction,SendInv,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv25_6e21_R30_1_I2 /\ SendInvAckAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv25_6e21_R30_1_I2 /\ RecvInvAckAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv25_6e21_R30_1_I2 /\ SendGntSAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv25_6e21_R30_1_I2 /\ SendGntEAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,Inv37_7204_R19_0_I1,SendGntEAction,SendGntE,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv25_6e21_R30_1_I2 /\ RecvGntSAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv25_6e21_R30_1_I2 /\ RecvGntEAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv25_6e21_R30_1_I2 /\ StoreAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,StoreAction,Store,Inv25_6e21_R30_1_I2
  \* (Inv25_6e21_R30_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv25_6e21_R30_1_I2 /\ SendReqSAction => Inv25_6e21_R30_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv25_6e21_R30_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv24_ba79_R32_1_I2
THEOREM L_15 == TypeOK /\ Inv16_d756_R1_2_I1 /\ Inv2275_b1ee_R34_0_I3 /\ Inv24_ba79_R32_1_I2 /\ Next => Inv24_ba79_R32_1_I2'
  \* (Inv24_ba79_R32_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv24_ba79_R32_1_I2 /\ SendReqEAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv24_ba79_R32_1_I2 /\ RecvReqSAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv24_ba79_R32_1_I2 /\ RecvReqEAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv24_ba79_R32_1_I2 /\ SendInvAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv24_ba79_R32_1_I2 /\ SendInvAckAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv24_ba79_R32_1_I2 /\ RecvInvAckAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv24_ba79_R32_1_I2 /\ SendGntSAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv16_d756_R1_2_I1 /\ Inv24_ba79_R32_1_I2 /\ SendGntEAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,Inv16_d756_R1_2_I1,SendGntEAction,SendGntE,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ Inv24_ba79_R32_1_I2 /\ RecvGntSAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,Inv2275_b1ee_R34_0_I3,RecvGntSAction,RecvGntS,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv24_ba79_R32_1_I2 /\ RecvGntEAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv24_ba79_R32_1_I2 /\ StoreAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,StoreAction,Store,Inv24_ba79_R32_1_I2
  \* (Inv24_ba79_R32_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv24_ba79_R32_1_I2 /\ SendReqSAction => Inv24_ba79_R32_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv24_ba79_R32_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2275_b1ee_R34_0_I3
THEOREM L_16 == TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv2275_b1ee_R34_0_I3 /\ Next => Inv2275_b1ee_R34_0_I3'
  \* (Inv2275_b1ee_R34_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ SendReqEAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ RecvReqSAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ RecvReqEAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ SendInvAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ SendInvAckAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ RecvInvAckAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ SendGntSAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv2275_b1ee_R34_0_I3 /\ SendGntEAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,Inv1_85ad_R3_0_I1,SendGntEAction,SendGntE,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ RecvGntSAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ RecvGntEAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ StoreAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,StoreAction,Store,Inv2275_b1ee_R34_0_I3
  \* (Inv2275_b1ee_R34_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ SendReqSAction => Inv2275_b1ee_R34_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2275_b1ee_R34_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv16_d756_R1_2_I1
THEOREM L_17 == TypeOK /\ Inv10_8267_R4_2_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv1_85ad_R3_0_I1 /\ Inv16_d756_R1_2_I1 /\ Next => Inv16_d756_R1_2_I1'
  \* (Inv16_d756_R1_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv16_d756_R1_2_I1 /\ SendReqEAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv16_d756_R1_2_I1 /\ RecvReqSAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv16_d756_R1_2_I1 /\ RecvReqEAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv16_d756_R1_2_I1 /\ SendInvAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv16_d756_R1_2_I1 /\ SendInvAckAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_8267_R4_2_I1 /\ Inv16_d756_R1_2_I1 /\ RecvInvAckAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,Inv10_8267_R4_2_I1,RecvInvAckAction,RecvInvAck,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv16_d756_R1_2_I1 /\ SendGntSAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv16_d756_R1_2_I1 /\ SendGntEAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv16_d756_R1_2_I1 /\ RecvGntSAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,Inv1_85ad_R3_0_I1,RecvGntSAction,RecvGntS,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv1_85ad_R3_0_I1 /\ Inv16_d756_R1_2_I1 /\ RecvGntEAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,Inv1_85ad_R3_0_I1,RecvGntEAction,RecvGntE,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv16_d756_R1_2_I1 /\ StoreAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,StoreAction,Store,Inv16_d756_R1_2_I1
  \* (Inv16_d756_R1_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv16_d756_R1_2_I1 /\ SendReqSAction => Inv16_d756_R1_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv16_d756_R1_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_8267_R4_2_I1
THEOREM L_18 == TypeOK /\ Inv11_c03f_R10_0_I1 /\ Inv11_c03f_R10_0_I1 /\ Inv10_8267_R4_2_I1 /\ Next => Inv10_8267_R4_2_I1'
  \* (Inv10_8267_R4_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv10_8267_R4_2_I1 /\ SendReqEAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv10_8267_R4_2_I1 /\ RecvReqSAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv10_8267_R4_2_I1 /\ RecvReqEAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_8267_R4_2_I1 /\ SendInvAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv10_8267_R4_2_I1 /\ SendInvAckAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_8267_R4_2_I1 /\ RecvInvAckAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv10_8267_R4_2_I1 /\ SendGntSAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv10_8267_R4_2_I1 /\ SendGntEAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_c03f_R10_0_I1 /\ Inv10_8267_R4_2_I1 /\ RecvGntSAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,Inv11_c03f_R10_0_I1,RecvGntSAction,RecvGntS,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv11_c03f_R10_0_I1 /\ Inv10_8267_R4_2_I1 /\ RecvGntEAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,Inv11_c03f_R10_0_I1,RecvGntEAction,RecvGntE,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv10_8267_R4_2_I1 /\ StoreAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,StoreAction,Store,Inv10_8267_R4_2_I1
  \* (Inv10_8267_R4_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv10_8267_R4_2_I1 /\ SendReqSAction => Inv10_8267_R4_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv10_8267_R4_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_c03f_R10_0_I1
THEOREM L_19 == TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv2801_c9e4_R13_1_I2 /\ Inv13_9e93_R13_0_I1 /\ Inv11_c03f_R10_0_I1 /\ Next => Inv11_c03f_R10_0_I1'
  \* (Inv11_c03f_R10_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv11_c03f_R10_0_I1 /\ SendReqEAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv11_c03f_R10_0_I1 /\ RecvReqSAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv11_c03f_R10_0_I1 /\ RecvReqEAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv11_c03f_R10_0_I1 /\ SendInvAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,Inv12_45c1_R13_2_I1,SendInvAction,SendInv,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_c03f_R10_0_I1 /\ SendInvAckAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv11_c03f_R10_0_I1 /\ RecvInvAckAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv2801_c9e4_R13_1_I2 /\ Inv11_c03f_R10_0_I1 /\ SendGntSAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,Inv2801_c9e4_R13_1_I2,SendGntSAction,SendGntS,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ Inv11_c03f_R10_0_I1 /\ SendGntEAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,Inv13_9e93_R13_0_I1,SendGntEAction,SendGntE,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_c03f_R10_0_I1 /\ RecvGntSAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv11_c03f_R10_0_I1 /\ RecvGntEAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv11_c03f_R10_0_I1 /\ StoreAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,StoreAction,Store,Inv11_c03f_R10_0_I1
  \* (Inv11_c03f_R10_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv11_c03f_R10_0_I1 /\ SendReqSAction => Inv11_c03f_R10_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv11_c03f_R10_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv580_b566_R32_1_I2
THEOREM L_20 == TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ Inv2351_aaa7_R35_0_I4 /\ Inv64_d564_R21_2_I1 /\ Inv580_b566_R32_1_I2 /\ Next => Inv580_b566_R32_1_I2'
  \* (Inv580_b566_R32_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv580_b566_R32_1_I2 /\ SendReqEAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ Inv580_b566_R32_1_I2 /\ RecvReqSAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,Inv2351_aaa7_R35_0_I4,RecvReqSAction,RecvReqS,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ Inv580_b566_R32_1_I2 /\ RecvReqEAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,Inv2351_aaa7_R35_0_I4,RecvReqEAction,RecvReqE,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv580_b566_R32_1_I2 /\ SendInvAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv64_d564_R21_2_I1 /\ Inv580_b566_R32_1_I2 /\ SendInvAckAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,Inv64_d564_R21_2_I1,SendInvAckAction,SendInvAck,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv580_b566_R32_1_I2 /\ RecvInvAckAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv580_b566_R32_1_I2 /\ SendGntSAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv580_b566_R32_1_I2 /\ SendGntEAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv580_b566_R32_1_I2 /\ RecvGntSAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv580_b566_R32_1_I2 /\ RecvGntEAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv580_b566_R32_1_I2 /\ StoreAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,StoreAction,Store,Inv580_b566_R32_1_I2
  \* (Inv580_b566_R32_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv580_b566_R32_1_I2 /\ SendReqSAction => Inv580_b566_R32_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv580_b566_R32_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2351_aaa7_R35_0_I4
THEOREM L_21 == TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv3402_aace_R38_0_I4 /\ Inv2351_aaa7_R35_0_I4 /\ Next => Inv2351_aaa7_R35_0_I4'
  \* (Inv2351_aaa7_R35_0_I4,SendReqEAction)
  <1>1. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ SendReqEAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,RecvReqSAction)
  <1>2. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ RecvReqSAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,RecvReqEAction)
  <1>3. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ RecvReqEAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,SendInvAction)
  <1>4. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ SendInvAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,SendInvAction,SendInv,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,SendInvAckAction)
  <1>5. TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv2351_aaa7_R35_0_I4 /\ SendInvAckAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,Inv342_1d58_R27_2_I2,SendInvAckAction,SendInvAck,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ RecvInvAckAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,SendGntSAction)
  <1>7. TypeOK /\ Inv3402_aace_R38_0_I4 /\ Inv2351_aaa7_R35_0_I4 /\ SendGntSAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,Inv3402_aace_R38_0_I4,SendGntSAction,SendGntS,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,SendGntEAction)
  <1>8. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ SendGntEAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,RecvGntSAction)
  <1>9. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ RecvGntSAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,RecvGntEAction)
  <1>10. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ RecvGntEAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,StoreAction)
  <1>11. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ StoreAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,StoreAction,Store,Inv2351_aaa7_R35_0_I4
  \* (Inv2351_aaa7_R35_0_I4,SendReqSAction)
  <1>12. TypeOK /\ Inv2351_aaa7_R35_0_I4 /\ SendReqSAction => Inv2351_aaa7_R35_0_I4' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2351_aaa7_R35_0_I4
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3402_aace_R38_0_I4
THEOREM L_22 == TypeOK /\ Inv2426_1275_R20_1_I2 /\ Inv3085_f335_R40_0_I2 /\ Inv1051_a1d6_R20_0_I3 /\ Inv24_ba79_R32_1_I2 /\ Inv3402_aace_R38_0_I4 /\ Next => Inv3402_aace_R38_0_I4'
  <1> USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE
  <1> USE NODE = {1,2,3} /\ DATA = {1,2}
  \* (Inv3402_aace_R38_0_I4,SendReqEAction)
  <1>1. TypeOK /\ Inv3402_aace_R38_0_I4 /\ SendReqEAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,RecvReqSAction)
  <1>2. TypeOK /\ Inv3402_aace_R38_0_I4 /\ RecvReqSAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,RecvReqEAction)
  <1>3. TypeOK /\ Inv3402_aace_R38_0_I4 /\ RecvReqEAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,SendInvAction)
  <1>4. TypeOK /\ Inv3402_aace_R38_0_I4 /\ SendInvAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,SendInvAction,SendInv,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,SendInvAckAction)
  <1>5. TypeOK /\ Inv2426_1275_R20_1_I2 /\ Inv3402_aace_R38_0_I4 /\ SendInvAckAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,Inv2426_1275_R20_1_I2,SendInvAckAction,SendInvAck,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3085_f335_R40_0_I2 /\ Inv1051_a1d6_R20_0_I3 /\ Inv24_ba79_R32_1_I2 /\ Inv3402_aace_R38_0_I4 /\ RecvInvAckAction => Inv3402_aace_R38_0_I4' 
    <2> SUFFICES ASSUME TypeOK /\ Inv3085_f335_R40_0_I2 /\ Inv1051_a1d6_R20_0_I3 /\ Inv24_ba79_R32_1_I2 /\ Inv3402_aace_R38_0_I4 /\ RecvInvAckAction,
                        NEW VARI \in NODE',
                        NEW VARJ \in NODE'
                 PROVE  ((Chan2[VARI].Cmd = "Inv") \/ ((CurCmd = "ReqE") \/ (~(Cache[VARJ].State = "I") \/ (~(ShrSet[VARJ]))) \/ ((ExGntd))) \/ (~(Chan2[VARJ].Cmd = "Empty")))'
      BY DEF Inv3402_aace_R38_0_I4
    <2> QED
      <3> SUFFICES ASSUME NEW i \in NODE,
                          RecvInvAck(i)
                   PROVE  ((Chan2[VARI].Cmd = "Inv") \/ ((CurCmd = "ReqE") \/ (~(Cache[VARJ].State = "I") \/ (~(ShrSet[VARJ]))) \/ ((ExGntd))) \/ (~(Chan2[VARJ].Cmd = "Empty")))'
        BY DEF RecvInvAckAction
      <3> QED
        <4>1. CASE ~ExGntd
            BY <4>1 DEF TypeOK,Inv3085_f335_R40_0_I2,Inv1051_a1d6_R20_0_I3,Inv24_ba79_R32_1_I2,RecvInvAckAction,RecvInvAck,Inv3402_aace_R38_0_I4
         <4>2. CASE ExGntd
            BY <4>2 DEF TypeOK,Inv3085_f335_R40_0_I2,Inv1051_a1d6_R20_0_I3,Inv24_ba79_R32_1_I2,RecvInvAckAction,RecvInvAck,Inv3402_aace_R38_0_I4
        <4>3. QED BY <4>1, <4>2
  \* (Inv3402_aace_R38_0_I4,SendGntSAction)
  <1>7. TypeOK /\ Inv3402_aace_R38_0_I4 /\ SendGntSAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,SendGntSAction,SendGntS,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,SendGntEAction)
  <1>8. TypeOK /\ Inv3402_aace_R38_0_I4 /\ SendGntEAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,SendGntEAction,SendGntE,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,RecvGntSAction)
  <1>9. TypeOK /\ Inv3402_aace_R38_0_I4 /\ RecvGntSAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,RecvGntEAction)
  <1>10. TypeOK /\ Inv3402_aace_R38_0_I4 /\ RecvGntEAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,StoreAction)
  <1>11. TypeOK /\ Inv3402_aace_R38_0_I4 /\ StoreAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,StoreAction,Store,Inv3402_aace_R38_0_I4
  \* (Inv3402_aace_R38_0_I4,SendReqSAction)
  <1>12. TypeOK /\ Inv3402_aace_R38_0_I4 /\ SendReqSAction => Inv3402_aace_R38_0_I4' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3402_aace_R38_0_I4
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3085_f335_R40_0_I2
THEOREM L_23 == TypeOK /\ Inv1031_515a_R30_2_I2 /\ Inv2275_b1ee_R34_0_I3 /\ Inv3990_3a8e_R0_1_I2 /\ Inv10_59dd_R42_1_I2 /\ Inv13_9e93_R13_0_I1 /\ Inv3085_f335_R40_0_I2 /\ Next => Inv3085_f335_R40_0_I2'
  \* (Inv3085_f335_R40_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv3085_f335_R40_0_I2 /\ SendReqEAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv3085_f335_R40_0_I2 /\ RecvReqSAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv3085_f335_R40_0_I2 /\ RecvReqEAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1031_515a_R30_2_I2 /\ Inv3085_f335_R40_0_I2 /\ SendInvAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,Inv1031_515a_R30_2_I2,SendInvAction,SendInv,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ Inv3990_3a8e_R0_1_I2 /\ Inv10_59dd_R42_1_I2 /\ Inv3085_f335_R40_0_I2 /\ SendInvAckAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,Inv2275_b1ee_R34_0_I3,Inv3990_3a8e_R0_1_I2,Inv10_59dd_R42_1_I2,SendInvAckAction,SendInvAck,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3085_f335_R40_0_I2 /\ RecvInvAckAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv3085_f335_R40_0_I2 /\ SendGntSAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ Inv3085_f335_R40_0_I2 /\ SendGntEAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,Inv13_9e93_R13_0_I1,SendGntEAction,SendGntE,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv3085_f335_R40_0_I2 /\ RecvGntSAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv3085_f335_R40_0_I2 /\ RecvGntEAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv3085_f335_R40_0_I2 /\ StoreAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,StoreAction,Store,Inv3085_f335_R40_0_I2
  \* (Inv3085_f335_R40_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv3085_f335_R40_0_I2 /\ SendReqSAction => Inv3085_f335_R40_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3085_f335_R40_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3990_3a8e_R0_1_I2
THEOREM L_24 == TypeOK /\ Inv2613_6920_R2_3_I2 /\ Inv11_513a_R2_1_I1 /\ Inv11_513a_R2_1_I1 /\ Inv1011_61c6_R1_0_I2 /\ Inv3990_3a8e_R0_1_I2 /\ Next => Inv3990_3a8e_R0_1_I2'
  \* (Inv3990_3a8e_R0_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ SendReqEAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ RecvReqSAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ RecvReqEAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2613_6920_R2_3_I2 /\ Inv3990_3a8e_R0_1_I2 /\ SendInvAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,Inv2613_6920_R2_3_I2,SendInvAction,SendInv,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ SendInvAckAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ RecvInvAckAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv11_513a_R2_1_I1 /\ Inv3990_3a8e_R0_1_I2 /\ SendGntSAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,Inv11_513a_R2_1_I1,SendGntSAction,SendGntS,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv11_513a_R2_1_I1 /\ Inv3990_3a8e_R0_1_I2 /\ SendGntEAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,Inv11_513a_R2_1_I1,SendGntEAction,SendGntE,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ RecvGntSAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1011_61c6_R1_0_I2 /\ Inv3990_3a8e_R0_1_I2 /\ RecvGntEAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,Inv1011_61c6_R1_0_I2,RecvGntEAction,RecvGntE,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ StoreAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,StoreAction,Store,Inv3990_3a8e_R0_1_I2
  \* (Inv3990_3a8e_R0_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ SendReqSAction => Inv3990_3a8e_R0_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3990_3a8e_R0_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_513a_R2_1_I1
THEOREM L_25 == TypeOK /\ Inv7_7199_R5_1_I1 /\ Inv4_a2c7_R3_1_I1 /\ Inv11_513a_R2_1_I1 /\ Next => Inv11_513a_R2_1_I1'
  \* (Inv11_513a_R2_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv11_513a_R2_1_I1 /\ SendReqEAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv11_513a_R2_1_I1 /\ RecvReqSAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv11_513a_R2_1_I1 /\ RecvReqEAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv11_513a_R2_1_I1 /\ SendInvAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv11_513a_R2_1_I1 /\ SendInvAckAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv7_7199_R5_1_I1 /\ Inv11_513a_R2_1_I1 /\ RecvInvAckAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,Inv7_7199_R5_1_I1,RecvInvAckAction,RecvInvAck,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv11_513a_R2_1_I1 /\ SendGntSAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv11_513a_R2_1_I1 /\ SendGntEAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv11_513a_R2_1_I1 /\ RecvGntSAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ Inv11_513a_R2_1_I1 /\ RecvGntEAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,Inv4_a2c7_R3_1_I1,RecvGntEAction,RecvGntE,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv11_513a_R2_1_I1 /\ StoreAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,StoreAction,Store,Inv11_513a_R2_1_I1
  \* (Inv11_513a_R2_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv11_513a_R2_1_I1 /\ SendReqSAction => Inv11_513a_R2_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv11_513a_R2_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4_a2c7_R3_1_I1
THEOREM L_26 == TypeOK /\ Inv13_5b11_R8_0_I1 /\ Inv4_a2c7_R3_1_I1 /\ Next => Inv4_a2c7_R3_1_I1'
  \* (Inv4_a2c7_R3_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ SendReqEAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ RecvReqSAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ RecvReqEAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ SendInvAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ SendInvAckAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv13_5b11_R8_0_I1 /\ Inv4_a2c7_R3_1_I1 /\ RecvInvAckAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,Inv13_5b11_R8_0_I1,RecvInvAckAction,RecvInvAck,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ SendGntSAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ SendGntEAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ RecvGntSAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ RecvGntEAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ StoreAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,StoreAction,Store,Inv4_a2c7_R3_1_I1
  \* (Inv4_a2c7_R3_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ SendReqSAction => Inv4_a2c7_R3_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv4_a2c7_R3_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv13_5b11_R8_0_I1
THEOREM L_27 == TypeOK /\ Inv55_c47d_R15_1_I1 /\ Inv13_9e93_R13_0_I1 /\ Inv13_5b11_R8_0_I1 /\ Next => Inv13_5b11_R8_0_I1'
  \* (Inv13_5b11_R8_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv13_5b11_R8_0_I1 /\ SendReqEAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv13_5b11_R8_0_I1 /\ RecvReqSAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv13_5b11_R8_0_I1 /\ RecvReqEAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv13_5b11_R8_0_I1 /\ SendInvAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv55_c47d_R15_1_I1 /\ Inv13_5b11_R8_0_I1 /\ SendInvAckAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,Inv55_c47d_R15_1_I1,SendInvAckAction,SendInvAck,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv13_5b11_R8_0_I1 /\ RecvInvAckAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv13_5b11_R8_0_I1 /\ SendGntSAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv13_9e93_R13_0_I1 /\ Inv13_5b11_R8_0_I1 /\ SendGntEAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,Inv13_9e93_R13_0_I1,SendGntEAction,SendGntE,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv13_5b11_R8_0_I1 /\ RecvGntSAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv13_5b11_R8_0_I1 /\ RecvGntEAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv13_5b11_R8_0_I1 /\ StoreAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,StoreAction,Store,Inv13_5b11_R8_0_I1
  \* (Inv13_5b11_R8_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv13_5b11_R8_0_I1 /\ SendReqSAction => Inv13_5b11_R8_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv13_5b11_R8_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv55_c47d_R15_1_I1
THEOREM L_28 == TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ Inv37_7204_R19_0_I1 /\ Inv55_c47d_R15_1_I1 /\ Next => Inv55_c47d_R15_1_I1'
  \* (Inv55_c47d_R15_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv55_c47d_R15_1_I1 /\ SendReqEAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv55_c47d_R15_1_I1 /\ RecvReqSAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv55_c47d_R15_1_I1 /\ RecvReqEAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ Inv55_c47d_R15_1_I1 /\ SendInvAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,Inv3533_fc2f_R3_2_I2,SendInvAction,SendInv,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv55_c47d_R15_1_I1 /\ SendInvAckAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv55_c47d_R15_1_I1 /\ RecvInvAckAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv55_c47d_R15_1_I1 /\ SendGntSAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv55_c47d_R15_1_I1 /\ SendGntEAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,Inv37_7204_R19_0_I1,SendGntEAction,SendGntE,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv55_c47d_R15_1_I1 /\ RecvGntSAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv55_c47d_R15_1_I1 /\ RecvGntEAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv55_c47d_R15_1_I1 /\ StoreAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,StoreAction,Store,Inv55_c47d_R15_1_I1
  \* (Inv55_c47d_R15_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv55_c47d_R15_1_I1 /\ SendReqSAction => Inv55_c47d_R15_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv55_c47d_R15_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3533_fc2f_R3_2_I2
THEOREM L_29 == TypeOK /\ Inv4026_ce35_R9_0_I2 /\ Inv4026_ce35_R9_0_I2 /\ Inv29_0f39_R9_2_I1 /\ Inv3533_fc2f_R3_2_I2 /\ Next => Inv3533_fc2f_R3_2_I2'
  \* (Inv3533_fc2f_R3_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ SendReqEAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ Inv3533_fc2f_R3_2_I2 /\ RecvReqSAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,Inv4026_ce35_R9_0_I2,RecvReqSAction,RecvReqS,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ Inv3533_fc2f_R3_2_I2 /\ RecvReqEAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,Inv4026_ce35_R9_0_I2,RecvReqEAction,RecvReqE,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ SendInvAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ SendInvAckAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ RecvInvAckAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ SendGntSAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv29_0f39_R9_2_I1 /\ Inv3533_fc2f_R3_2_I2 /\ SendGntEAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,Inv29_0f39_R9_2_I1,SendGntEAction,SendGntE,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ RecvGntSAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ RecvGntEAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ StoreAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,StoreAction,Store,Inv3533_fc2f_R3_2_I2
  \* (Inv3533_fc2f_R3_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ SendReqSAction => Inv3533_fc2f_R3_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3533_fc2f_R3_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4026_ce35_R9_0_I2
THEOREM L_30 == TypeOK /\ Inv4_a2c7_R3_1_I1 /\ Inv4_a2c7_R3_1_I1 /\ Inv4026_ce35_R9_0_I2 /\ Next => Inv4026_ce35_R9_0_I2'
  \* (Inv4026_ce35_R9_0_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ SendReqEAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ RecvReqSAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ RecvReqEAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,SendInvAction)
  <1>4. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ SendInvAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ SendInvAckAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ RecvInvAckAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ Inv4026_ce35_R9_0_I2 /\ SendGntSAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,Inv4_a2c7_R3_1_I1,SendGntSAction,SendGntS,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv4_a2c7_R3_1_I1 /\ Inv4026_ce35_R9_0_I2 /\ SendGntEAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,Inv4_a2c7_R3_1_I1,SendGntEAction,SendGntE,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ RecvGntSAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ RecvGntEAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,StoreAction)
  <1>11. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ StoreAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,StoreAction,Store,Inv4026_ce35_R9_0_I2
  \* (Inv4026_ce35_R9_0_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ SendReqSAction => Inv4026_ce35_R9_0_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv4026_ce35_R9_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv29_0f39_R9_2_I1
THEOREM L_31 == TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv29_0f39_R9_2_I1 /\ Next => Inv29_0f39_R9_2_I1'
  \* (Inv29_0f39_R9_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv29_0f39_R9_2_I1 /\ SendReqEAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv29_0f39_R9_2_I1 /\ RecvReqSAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv29_0f39_R9_2_I1 /\ RecvReqEAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv29_0f39_R9_2_I1 /\ SendInvAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv29_0f39_R9_2_I1 /\ SendInvAckAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv12_45c1_R13_2_I1 /\ Inv29_0f39_R9_2_I1 /\ RecvInvAckAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,Inv12_45c1_R13_2_I1,RecvInvAckAction,RecvInvAck,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv29_0f39_R9_2_I1 /\ SendGntSAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv29_0f39_R9_2_I1 /\ SendGntEAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv29_0f39_R9_2_I1 /\ RecvGntSAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv29_0f39_R9_2_I1 /\ RecvGntEAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv29_0f39_R9_2_I1 /\ StoreAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,StoreAction,Store,Inv29_0f39_R9_2_I1
  \* (Inv29_0f39_R9_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv29_0f39_R9_2_I1 /\ SendReqSAction => Inv29_0f39_R9_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv29_0f39_R9_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv7_7199_R5_1_I1
THEOREM L_32 == TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ Inv13_5b11_R8_0_I1 /\ Inv7_7199_R5_1_I1 /\ Next => Inv7_7199_R5_1_I1'
  \* (Inv7_7199_R5_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv7_7199_R5_1_I1 /\ SendReqEAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv7_7199_R5_1_I1 /\ RecvReqSAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv7_7199_R5_1_I1 /\ RecvReqEAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv7_7199_R5_1_I1 /\ SendInvAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv3990_3a8e_R0_1_I2 /\ Inv7_7199_R5_1_I1 /\ SendInvAckAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,Inv3990_3a8e_R0_1_I2,SendInvAckAction,SendInvAck,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv7_7199_R5_1_I1 /\ RecvInvAckAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv7_7199_R5_1_I1 /\ SendGntSAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv7_7199_R5_1_I1 /\ SendGntEAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv7_7199_R5_1_I1 /\ RecvGntSAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv13_5b11_R8_0_I1 /\ Inv7_7199_R5_1_I1 /\ RecvGntEAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,Inv13_5b11_R8_0_I1,RecvGntEAction,RecvGntE,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv7_7199_R5_1_I1 /\ StoreAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,StoreAction,Store,Inv7_7199_R5_1_I1
  \* (Inv7_7199_R5_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv7_7199_R5_1_I1 /\ SendReqSAction => Inv7_7199_R5_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv7_7199_R5_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2613_6920_R2_3_I2
THEOREM L_33 == TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ Inv8303_b7f8_R6_1_I2 /\ Inv3533_fc2f_R3_2_I2 /\ Inv2613_6920_R2_3_I2 /\ Next => Inv2613_6920_R2_3_I2'
  \* (Inv2613_6920_R2_3_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2613_6920_R2_3_I2 /\ SendReqEAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ Inv2613_6920_R2_3_I2 /\ RecvReqSAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,Inv8303_b7f8_R6_1_I2,RecvReqSAction,RecvReqS,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ Inv2613_6920_R2_3_I2 /\ RecvReqEAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,Inv8303_b7f8_R6_1_I2,RecvReqEAction,RecvReqE,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2613_6920_R2_3_I2 /\ SendInvAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv2613_6920_R2_3_I2 /\ SendInvAckAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv2613_6920_R2_3_I2 /\ RecvInvAckAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2613_6920_R2_3_I2 /\ SendGntSAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv2613_6920_R2_3_I2 /\ SendGntEAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2613_6920_R2_3_I2 /\ RecvGntSAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv3533_fc2f_R3_2_I2 /\ Inv2613_6920_R2_3_I2 /\ RecvGntEAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,Inv3533_fc2f_R3_2_I2,RecvGntEAction,RecvGntE,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,StoreAction)
  <1>11. TypeOK /\ Inv2613_6920_R2_3_I2 /\ StoreAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,StoreAction,Store,Inv2613_6920_R2_3_I2
  \* (Inv2613_6920_R2_3_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2613_6920_R2_3_I2 /\ SendReqSAction => Inv2613_6920_R2_3_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2613_6920_R2_3_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv8303_b7f8_R6_1_I2
THEOREM L_34 == TypeOK /\ Inv11_513a_R2_1_I1 /\ Inv11_513a_R2_1_I1 /\ Inv4026_ce35_R9_0_I2 /\ Inv8303_b7f8_R6_1_I2 /\ Next => Inv8303_b7f8_R6_1_I2'
  \* (Inv8303_b7f8_R6_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ SendReqEAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ RecvReqSAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ RecvReqEAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ SendInvAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ SendInvAckAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ RecvInvAckAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv11_513a_R2_1_I1 /\ Inv8303_b7f8_R6_1_I2 /\ SendGntSAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,Inv11_513a_R2_1_I1,SendGntSAction,SendGntS,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv11_513a_R2_1_I1 /\ Inv8303_b7f8_R6_1_I2 /\ SendGntEAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,Inv11_513a_R2_1_I1,SendGntEAction,SendGntE,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ RecvGntSAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv4026_ce35_R9_0_I2 /\ Inv8303_b7f8_R6_1_I2 /\ RecvGntEAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,Inv4026_ce35_R9_0_I2,RecvGntEAction,RecvGntE,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ StoreAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,StoreAction,Store,Inv8303_b7f8_R6_1_I2
  \* (Inv8303_b7f8_R6_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv8303_b7f8_R6_1_I2 /\ SendReqSAction => Inv8303_b7f8_R6_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv8303_b7f8_R6_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_59dd_R42_1_I2
THEOREM L_35 == TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ Inv2613_6920_R2_3_I2 /\ Inv24_ba79_R32_1_I2 /\ Inv580_b566_R32_1_I2 /\ Inv37_7204_R19_0_I1 /\ Inv10_59dd_R42_1_I2 /\ Next => Inv10_59dd_R42_1_I2'
  <1> USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE
  \* (Inv10_59dd_R42_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv10_59dd_R42_1_I2 /\ SendReqEAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv10_59dd_R42_1_I2 /\ RecvReqSAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv10_59dd_R42_1_I2 /\ RecvReqEAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2275_b1ee_R34_0_I3 /\ Inv2613_6920_R2_3_I2 /\ Inv24_ba79_R32_1_I2 /\ Inv580_b566_R32_1_I2 /\ Inv10_59dd_R42_1_I2 /\ SendInvAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,Inv2275_b1ee_R34_0_I3,Inv2613_6920_R2_3_I2,Inv24_ba79_R32_1_I2,Inv580_b566_R32_1_I2,SendInvAction,SendInv,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv10_59dd_R42_1_I2 /\ SendInvAckAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_59dd_R42_1_I2 /\ RecvInvAckAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv10_59dd_R42_1_I2 /\ SendGntSAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv10_59dd_R42_1_I2 /\ SendGntEAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,Inv37_7204_R19_0_I1,SendGntEAction,SendGntE,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv10_59dd_R42_1_I2 /\ RecvGntSAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv10_59dd_R42_1_I2 /\ RecvGntEAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv10_59dd_R42_1_I2 /\ StoreAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,StoreAction,Store,Inv10_59dd_R42_1_I2
  \* (Inv10_59dd_R42_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv10_59dd_R42_1_I2 /\ SendReqSAction => Inv10_59dd_R42_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv10_59dd_R42_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1031_515a_R30_2_I2
THEOREM L_36 == TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv2088_575b_R21_0_I2 /\ Inv1290_ee95_R33_3_I2 /\ Inv29_0f39_R9_2_I1 /\ Inv1031_515a_R30_2_I2 /\ Next => Inv1031_515a_R30_2_I2'
  \* (Inv1031_515a_R30_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1031_515a_R30_2_I2 /\ SendReqEAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv1031_515a_R30_2_I2 /\ RecvReqSAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,Inv2088_575b_R21_0_I2,RecvReqSAction,RecvReqS,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv1031_515a_R30_2_I2 /\ RecvReqEAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,Inv2088_575b_R21_0_I2,RecvReqEAction,RecvReqE,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv1031_515a_R30_2_I2 /\ SendInvAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ Inv1031_515a_R30_2_I2 /\ SendInvAckAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,Inv1290_ee95_R33_3_I2,SendInvAckAction,SendInvAck,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1031_515a_R30_2_I2 /\ RecvInvAckAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1031_515a_R30_2_I2 /\ SendGntSAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv29_0f39_R9_2_I1 /\ Inv1031_515a_R30_2_I2 /\ SendGntEAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,Inv29_0f39_R9_2_I1,SendGntEAction,SendGntE,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1031_515a_R30_2_I2 /\ RecvGntSAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1031_515a_R30_2_I2 /\ RecvGntEAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv1031_515a_R30_2_I2 /\ StoreAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,StoreAction,Store,Inv1031_515a_R30_2_I2
  \* (Inv1031_515a_R30_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1031_515a_R30_2_I2 /\ SendReqSAction => Inv1031_515a_R30_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1031_515a_R30_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1290_ee95_R33_3_I2
THEOREM L_37 == TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv342_1d58_R27_2_I2 /\ Inv3928_4fdf_R36_3_I3 /\ Inv29_0f39_R9_2_I1 /\ Inv1290_ee95_R33_3_I2 /\ Next => Inv1290_ee95_R33_3_I2'
  \* (Inv1290_ee95_R33_3_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ SendReqEAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv1290_ee95_R33_3_I2 /\ RecvReqSAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,Inv342_1d58_R27_2_I2,RecvReqSAction,RecvReqS,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv1290_ee95_R33_3_I2 /\ RecvReqEAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,Inv342_1d58_R27_2_I2,RecvReqEAction,RecvReqE,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,SendInvAction)
  <1>4. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ Inv1290_ee95_R33_3_I2 /\ SendInvAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,Inv3928_4fdf_R36_3_I3,SendInvAction,SendInv,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ SendInvAckAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ RecvInvAckAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ SendGntSAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv29_0f39_R9_2_I1 /\ Inv1290_ee95_R33_3_I2 /\ SendGntEAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,Inv29_0f39_R9_2_I1,SendGntEAction,SendGntE,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ RecvGntSAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ RecvGntEAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,StoreAction)
  <1>11. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ StoreAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,StoreAction,Store,Inv1290_ee95_R33_3_I2
  \* (Inv1290_ee95_R33_3_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv1290_ee95_R33_3_I2 /\ SendReqSAction => Inv1290_ee95_R33_3_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv1290_ee95_R33_3_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv342_1d58_R27_2_I2
THEOREM L_38 == TypeOK /\ Inv2426_1275_R20_1_I2 /\ Inv37_7204_R19_0_I1 /\ Inv342_1d58_R27_2_I2 /\ Next => Inv342_1d58_R27_2_I2'
  \* (Inv342_1d58_R27_2_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv342_1d58_R27_2_I2 /\ SendReqEAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv342_1d58_R27_2_I2 /\ RecvReqSAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv342_1d58_R27_2_I2 /\ RecvReqEAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,SendInvAction)
  <1>4. TypeOK /\ Inv342_1d58_R27_2_I2 /\ SendInvAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv342_1d58_R27_2_I2 /\ SendInvAckAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv342_1d58_R27_2_I2 /\ RecvInvAckAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2426_1275_R20_1_I2 /\ Inv342_1d58_R27_2_I2 /\ SendGntSAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,Inv2426_1275_R20_1_I2,SendGntSAction,SendGntS,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv37_7204_R19_0_I1 /\ Inv342_1d58_R27_2_I2 /\ SendGntEAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,Inv37_7204_R19_0_I1,SendGntEAction,SendGntE,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv342_1d58_R27_2_I2 /\ RecvGntSAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv342_1d58_R27_2_I2 /\ RecvGntEAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,StoreAction)
  <1>11. TypeOK /\ Inv342_1d58_R27_2_I2 /\ StoreAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,StoreAction,Store,Inv342_1d58_R27_2_I2
  \* (Inv342_1d58_R27_2_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv342_1d58_R27_2_I2 /\ SendReqSAction => Inv342_1d58_R27_2_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv342_1d58_R27_2_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2426_1275_R20_1_I2
THEOREM L_39 == TypeOK /\ Inv4944_1b30_R25_1_I2 /\ Inv2426_1275_R20_1_I2 /\ Next => Inv2426_1275_R20_1_I2'
  \* (Inv2426_1275_R20_1_I2,SendReqEAction)
  <1>1. TypeOK /\ Inv2426_1275_R20_1_I2 /\ SendReqEAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,SendReqEAction,SendReqE,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,RecvReqSAction)
  <1>2. TypeOK /\ Inv2426_1275_R20_1_I2 /\ RecvReqSAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,RecvReqEAction)
  <1>3. TypeOK /\ Inv2426_1275_R20_1_I2 /\ RecvReqEAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,SendInvAction)
  <1>4. TypeOK /\ Inv2426_1275_R20_1_I2 /\ SendInvAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,SendInvAction,SendInv,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,SendInvAckAction)
  <1>5. TypeOK /\ Inv2426_1275_R20_1_I2 /\ SendInvAckAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,RecvInvAckAction)
  <1>6. TypeOK /\ Inv4944_1b30_R25_1_I2 /\ Inv2426_1275_R20_1_I2 /\ RecvInvAckAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,Inv4944_1b30_R25_1_I2,RecvInvAckAction,RecvInvAck,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,SendGntSAction)
  <1>7. TypeOK /\ Inv2426_1275_R20_1_I2 /\ SendGntSAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,SendGntSAction,SendGntS,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,SendGntEAction)
  <1>8. TypeOK /\ Inv2426_1275_R20_1_I2 /\ SendGntEAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,SendGntEAction,SendGntE,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,RecvGntSAction)
  <1>9. TypeOK /\ Inv2426_1275_R20_1_I2 /\ RecvGntSAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,RecvGntEAction)
  <1>10. TypeOK /\ Inv2426_1275_R20_1_I2 /\ RecvGntEAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,StoreAction)
  <1>11. TypeOK /\ Inv2426_1275_R20_1_I2 /\ StoreAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,StoreAction,Store,Inv2426_1275_R20_1_I2
  \* (Inv2426_1275_R20_1_I2,SendReqSAction)
  <1>12. TypeOK /\ Inv2426_1275_R20_1_I2 /\ SendReqSAction => Inv2426_1275_R20_1_I2' BY DEF TypeOK,SendReqSAction,SendReqS,Inv2426_1275_R20_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3928_4fdf_R36_3_I3
THEOREM L_40 == TypeOK /\ Inv8711_7c56_R39_0_I3 /\ Inv8711_7c56_R39_0_I3 /\ Inv29_0f39_R9_2_I1 /\ Inv3928_4fdf_R36_3_I3 /\ Next => Inv3928_4fdf_R36_3_I3'
  \* (Inv3928_4fdf_R36_3_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ SendReqEAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ Inv3928_4fdf_R36_3_I3 /\ RecvReqSAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,Inv8711_7c56_R39_0_I3,RecvReqSAction,RecvReqS,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ Inv3928_4fdf_R36_3_I3 /\ RecvReqEAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,Inv8711_7c56_R39_0_I3,RecvReqEAction,RecvReqE,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,SendInvAction)
  <1>4. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ SendInvAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ SendInvAckAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ RecvInvAckAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ SendGntSAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv29_0f39_R9_2_I1 /\ Inv3928_4fdf_R36_3_I3 /\ SendGntEAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,Inv29_0f39_R9_2_I1,SendGntEAction,SendGntE,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ RecvGntSAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ RecvGntEAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,StoreAction)
  <1>11. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ StoreAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,StoreAction,Store,Inv3928_4fdf_R36_3_I3
  \* (Inv3928_4fdf_R36_3_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv3928_4fdf_R36_3_I3 /\ SendReqSAction => Inv3928_4fdf_R36_3_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv3928_4fdf_R36_3_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv8711_7c56_R39_0_I3
THEOREM L_41 == TypeOK /\ Inv8711_7c56_R39_0_I3 /\ Next => Inv8711_7c56_R39_0_I3'
  \* (Inv8711_7c56_R39_0_I3,SendReqEAction)
  <1>1. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ SendReqEAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,SendReqEAction,SendReqE,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,RecvReqSAction)
  <1>2. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ RecvReqSAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,RecvReqEAction)
  <1>3. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ RecvReqEAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,SendInvAction)
  <1>4. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ SendInvAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,SendInvAction,SendInv,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,SendInvAckAction)
  <1>5. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ SendInvAckAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,RecvInvAckAction)
  <1>6. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ RecvInvAckAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,SendGntSAction)
  <1>7. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ SendGntSAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,SendGntSAction,SendGntS,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,SendGntEAction)
  <1>8. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ SendGntEAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,SendGntEAction,SendGntE,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,RecvGntSAction)
  <1>9. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ RecvGntSAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,RecvGntEAction)
  <1>10. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ RecvGntEAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,StoreAction)
  <1>11. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ StoreAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,StoreAction,Store,Inv8711_7c56_R39_0_I3
  \* (Inv8711_7c56_R39_0_I3,SendReqSAction)
  <1>12. TypeOK /\ Inv8711_7c56_R39_0_I3 /\ SendReqSAction => Inv8711_7c56_R39_0_I3' BY DEF TypeOK,SendReqSAction,SendReqS,Inv8711_7c56_R39_0_I3
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv64_d564_R21_2_I1
THEOREM L_42 == TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv342_1d58_R27_2_I2 /\ Inv64_d564_R21_2_I1 /\ Next => Inv64_d564_R21_2_I1'
  \* (Inv64_d564_R21_2_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv64_d564_R21_2_I1 /\ SendReqEAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv64_d564_R21_2_I1 /\ RecvReqSAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,Inv342_1d58_R27_2_I2,RecvReqSAction,RecvReqS,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv342_1d58_R27_2_I2 /\ Inv64_d564_R21_2_I1 /\ RecvReqEAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,Inv342_1d58_R27_2_I2,RecvReqEAction,RecvReqE,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,SendInvAction)
  <1>4. TypeOK /\ Inv64_d564_R21_2_I1 /\ SendInvAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv64_d564_R21_2_I1 /\ SendInvAckAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv64_d564_R21_2_I1 /\ RecvInvAckAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv64_d564_R21_2_I1 /\ SendGntSAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv64_d564_R21_2_I1 /\ SendGntEAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv64_d564_R21_2_I1 /\ RecvGntSAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv64_d564_R21_2_I1 /\ RecvGntEAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,StoreAction)
  <1>11. TypeOK /\ Inv64_d564_R21_2_I1 /\ StoreAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,StoreAction,Store,Inv64_d564_R21_2_I1
  \* (Inv64_d564_R21_2_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv64_d564_R21_2_I1 /\ SendReqSAction => Inv64_d564_R21_2_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv64_d564_R21_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_84e4_R7_1_I1
THEOREM L_43 == TypeOK /\ Inv10_259c_R14_0_I1 /\ Inv10_84e4_R7_1_I1 /\ Next => Inv10_84e4_R7_1_I1'
  \* (Inv10_84e4_R7_1_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv10_84e4_R7_1_I1 /\ SendReqEAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv10_84e4_R7_1_I1 /\ RecvReqSAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,RecvReqSAction,RecvReqS,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv10_84e4_R7_1_I1 /\ RecvReqEAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,RecvReqEAction,RecvReqE,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_84e4_R7_1_I1 /\ SendInvAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv10_84e4_R7_1_I1 /\ SendInvAckAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,SendInvAckAction,SendInvAck,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_259c_R14_0_I1 /\ Inv10_84e4_R7_1_I1 /\ RecvInvAckAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,Inv10_259c_R14_0_I1,RecvInvAckAction,RecvInvAck,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv10_84e4_R7_1_I1 /\ SendGntSAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv10_84e4_R7_1_I1 /\ SendGntEAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv10_84e4_R7_1_I1 /\ RecvGntSAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv10_84e4_R7_1_I1 /\ RecvGntEAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,StoreAction)
  <1>11. TypeOK /\ Inv10_84e4_R7_1_I1 /\ StoreAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,StoreAction,Store,Inv10_84e4_R7_1_I1
  \* (Inv10_84e4_R7_1_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv10_84e4_R7_1_I1 /\ SendReqSAction => Inv10_84e4_R7_1_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv10_84e4_R7_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_259c_R14_0_I1
THEOREM L_44 == TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv2088_575b_R21_0_I2 /\ Inv64_d564_R21_2_I1 /\ Inv10_259c_R14_0_I1 /\ Next => Inv10_259c_R14_0_I1'
  \* (Inv10_259c_R14_0_I1,SendReqEAction)
  <1>1. TypeOK /\ Inv10_259c_R14_0_I1 /\ SendReqEAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,SendReqEAction,SendReqE,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,RecvReqSAction)
  <1>2. TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv10_259c_R14_0_I1 /\ RecvReqSAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,Inv2088_575b_R21_0_I2,RecvReqSAction,RecvReqS,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,RecvReqEAction)
  <1>3. TypeOK /\ Inv2088_575b_R21_0_I2 /\ Inv10_259c_R14_0_I1 /\ RecvReqEAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,Inv2088_575b_R21_0_I2,RecvReqEAction,RecvReqE,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,SendInvAction)
  <1>4. TypeOK /\ Inv10_259c_R14_0_I1 /\ SendInvAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,SendInvAction,SendInv,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,SendInvAckAction)
  <1>5. TypeOK /\ Inv64_d564_R21_2_I1 /\ Inv10_259c_R14_0_I1 /\ SendInvAckAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,Inv64_d564_R21_2_I1,SendInvAckAction,SendInvAck,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,RecvInvAckAction)
  <1>6. TypeOK /\ Inv10_259c_R14_0_I1 /\ RecvInvAckAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,RecvInvAckAction,RecvInvAck,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,SendGntSAction)
  <1>7. TypeOK /\ Inv10_259c_R14_0_I1 /\ SendGntSAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,SendGntSAction,SendGntS,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,SendGntEAction)
  <1>8. TypeOK /\ Inv10_259c_R14_0_I1 /\ SendGntEAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,SendGntEAction,SendGntE,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,RecvGntSAction)
  <1>9. TypeOK /\ Inv10_259c_R14_0_I1 /\ RecvGntSAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,RecvGntSAction,RecvGntS,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,RecvGntEAction)
  <1>10. TypeOK /\ Inv10_259c_R14_0_I1 /\ RecvGntEAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,RecvGntEAction,RecvGntE,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,StoreAction)
  <1>11. TypeOK /\ Inv10_259c_R14_0_I1 /\ StoreAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,StoreAction,Store,Inv10_259c_R14_0_I1
  \* (Inv10_259c_R14_0_I1,SendReqSAction)
  <1>12. TypeOK /\ Inv10_259c_R14_0_I1 /\ SendReqSAction => Inv10_259c_R14_0_I1' BY DEF TypeOK,SendReqSAction,SendReqS,Inv10_259c_R14_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE DEF MSG, MSG_CMD, CACHE, CACHE_STATE
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
    <1>2. Init => Inv104_03a2_R0_0_I1 BY DEF Init, Inv104_03a2_R0_0_I1, IndGlobal
    <1>3. Init => Inv1011_61c6_R1_0_I2 BY DEF Init, Inv1011_61c6_R1_0_I2, IndGlobal
    <1>4. Init => Inv1_85ad_R3_0_I1 BY DEF Init, Inv1_85ad_R3_0_I1, IndGlobal
    <1>5. Init => Inv1_eb94_R7_0_I1 BY DEF Init, Inv1_eb94_R7_0_I1, IndGlobal
    <1>6. Init => Inv13_9e93_R13_0_I1 BY DEF Init, Inv13_9e93_R13_0_I1, IndGlobal
    <1>7. Init => Inv37_7204_R19_0_I1 BY DEF Init, Inv37_7204_R19_0_I1, IndGlobal
    <1>8. Init => Inv18_5035_R24_0_I1 BY DEF Init, Inv18_5035_R24_0_I1, IndGlobal
    <1>9. Init => Inv12_45c1_R13_2_I1 BY DEF Init, Inv12_45c1_R13_2_I1, IndGlobal
    <1>10. Init => Inv2088_575b_R21_0_I2 BY DEF Init, Inv2088_575b_R21_0_I2, IndGlobal
    <1>11. Init => Inv2801_c9e4_R13_1_I2 BY DEF Init, Inv2801_c9e4_R13_1_I2, IndGlobal
    <1>12. Init => Inv1051_a1d6_R20_0_I3 BY DEF Init, Inv1051_a1d6_R20_0_I3, IndGlobal
    <1>13. Init => Inv4944_1b30_R25_1_I2 BY DEF Init, Inv4944_1b30_R25_1_I2, IndGlobal
    <1>14. Init => Inv25_6e21_R30_1_I2 BY DEF Init, Inv25_6e21_R30_1_I2, IndGlobal
    <1>15. Init => Inv24_ba79_R32_1_I2 BY DEF Init, Inv24_ba79_R32_1_I2, IndGlobal
    <1>16. Init => Inv2275_b1ee_R34_0_I3 BY DEF Init, Inv2275_b1ee_R34_0_I3, IndGlobal
    <1>17. Init => Inv16_d756_R1_2_I1 BY DEF Init, Inv16_d756_R1_2_I1, IndGlobal
    <1>18. Init => Inv10_8267_R4_2_I1 BY DEF Init, Inv10_8267_R4_2_I1, IndGlobal
    <1>19. Init => Inv11_c03f_R10_0_I1 BY DEF Init, Inv11_c03f_R10_0_I1, IndGlobal
    <1>20. Init => Inv580_b566_R32_1_I2 BY DEF Init, Inv580_b566_R32_1_I2, IndGlobal
    <1>21. Init => Inv2351_aaa7_R35_0_I4 BY DEF Init, Inv2351_aaa7_R35_0_I4, IndGlobal
    <1>22. Init => Inv3402_aace_R38_0_I4 BY DEF Init, Inv3402_aace_R38_0_I4, IndGlobal
    <1>23. Init => Inv3085_f335_R40_0_I2 BY DEF Init, Inv3085_f335_R40_0_I2, IndGlobal
    <1>24. Init => Inv3990_3a8e_R0_1_I2 BY DEF Init, Inv3990_3a8e_R0_1_I2, IndGlobal
    <1>25. Init => Inv11_513a_R2_1_I1 BY DEF Init, Inv11_513a_R2_1_I1, IndGlobal
    <1>26. Init => Inv4_a2c7_R3_1_I1 BY DEF Init, Inv4_a2c7_R3_1_I1, IndGlobal
    <1>27. Init => Inv13_5b11_R8_0_I1 BY DEF Init, Inv13_5b11_R8_0_I1, IndGlobal
    <1>28. Init => Inv55_c47d_R15_1_I1 BY DEF Init, Inv55_c47d_R15_1_I1, IndGlobal
    <1>29. Init => Inv3533_fc2f_R3_2_I2 BY DEF Init, Inv3533_fc2f_R3_2_I2, IndGlobal
    <1>30. Init => Inv4026_ce35_R9_0_I2 BY DEF Init, Inv4026_ce35_R9_0_I2, IndGlobal
    <1>31. Init => Inv29_0f39_R9_2_I1 BY DEF Init, Inv29_0f39_R9_2_I1, IndGlobal
    <1>32. Init => Inv7_7199_R5_1_I1 BY DEF Init, Inv7_7199_R5_1_I1, IndGlobal
    <1>33. Init => Inv2613_6920_R2_3_I2 BY DEF Init, Inv2613_6920_R2_3_I2, IndGlobal
    <1>34. Init => Inv8303_b7f8_R6_1_I2 BY DEF Init, Inv8303_b7f8_R6_1_I2, IndGlobal
    <1>35. Init => Inv10_59dd_R42_1_I2 BY DEF Init, Inv10_59dd_R42_1_I2, IndGlobal
    <1>36. Init => Inv1031_515a_R30_2_I2 BY DEF Init, Inv1031_515a_R30_2_I2, IndGlobal
    <1>37. Init => Inv1290_ee95_R33_3_I2 BY DEF Init, Inv1290_ee95_R33_3_I2, IndGlobal
    <1>38. Init => Inv342_1d58_R27_2_I2 BY DEF Init, Inv342_1d58_R27_2_I2, IndGlobal
    <1>39. Init => Inv2426_1275_R20_1_I2 BY DEF Init, Inv2426_1275_R20_1_I2, IndGlobal
    <1>40. Init => Inv3928_4fdf_R36_3_I3 BY DEF Init, Inv3928_4fdf_R36_3_I3, IndGlobal
    <1>41. Init => Inv8711_7c56_R39_0_I3 BY DEF Init, Inv8711_7c56_R39_0_I3, IndGlobal
    <1>42. Init => Inv64_d564_R21_2_I1 BY DEF Init, Inv64_d564_R21_2_I1, IndGlobal
    <1>43. Init => Inv10_84e4_R7_1_I1 BY DEF Init, Inv10_84e4_R7_1_I1, IndGlobal
    <1>44. Init => Inv10_259c_R14_0_I1 BY DEF Init, Inv10_259c_R14_0_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36,<1>37,<1>38,<1>39,<1>40,<1>41,<1>42,<1>43,<1>44 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36,L_37,L_38,L_39,L_40,L_41,L_42,L_43,L_44 DEF Next, IndGlobal


====