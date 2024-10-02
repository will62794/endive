------------------------------- MODULE Bakery_IndProofs -------------------------------
EXTENDS Bakery, FiniteSets, TLAPS, FiniteSetTheorems



\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 27
\* num proof obligations: 378
Safety == H_MutualExclusion
Inv4690_2f61_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "cs")) \/ (~(pc[VARJ] = "w1"))
Inv4520_48f3_R1_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI})))
Inv24959_7f87_R1_1_I2 == \A VARJ \in Procs : (pc[VARJ] = "e2") \/ ((unchecked[VARJ] = {})) \/ ((pc[VARJ] \in {"w1","w2"}))
Inv5819_32cd_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "w2")))
Inv4576_59b1_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "cs")) \/ (~(pc[VARJ] = "w2"))
Inv4521_3f08_R1_1_I2 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "cs"))
Inv10_8778_R2_0_I3 == \A VARJ \in Procs : ~(VARJ \in unchecked[VARJ])
Inv5742_3d78_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "w2"))) \/ (~(pc[VARJ] = "w2"))
Inv80_b6ff_R2_0_I3 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] \in {"w1","w2"}))
Inv1922_5e75_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1")))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}))
Inv4606_2f6b_R5_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(pc[VARJ] = "cs"))
Inv11_3838_R8_0_I2 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
Inv61_df69_R8_0_I2 == \A VARI \in Procs : (nxt[VARI] \in unchecked[VARI]) \/ (~(pc[VARI] = "w2"))
Inv1028_6ea5_R8_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1")))) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))
Inv140_f68c_R9_0_I1 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "e4"))
Inv4227_eecc_R10_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] \in {"e4","w1","w2"}))
Inv32498_2818_R11_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e3") \/ (~(pc[VARJ] = "cs")))
Inv2740_e784_R16_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(max[VARI] < num[VARJ])) \/ (~(pc[VARI] = "e3")) \/ (~(pc[VARJ] \in {"w1","w2"}))
Inv3293_1a1e_R17_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARI] = "e2")) \/ (~(pc[VARJ] = "cs")) \/ (~(max[VARI] < num[VARJ]))
Inv0_b3ba_R18_0_I0 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))
Inv6093_1c74_R18_1_I2 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3"))) \/ (~(pc[VARI] = "w2"))
Inv19_037d_R19_0_I1 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ (~(unchecked[VARI] = {}))
Inv1_b58a_R20_0_I1 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ ((VARJ \in unchecked[VARI]))
Inv350_b077_R20_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ (~(nxt[VARI] = VARJ)) \/ (~(pc[VARI] = "w2"))
Inv103_c9b1_R21_1_I1 == \A VARJ \in Procs : (flag[VARJ]) \/ (~(pc[VARJ] = "e3"))
Inv40_180c_R24_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e2"))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv4690_2f61_R0_0_I2
  /\ Inv4520_48f3_R1_0_I2
  /\ Inv10_8778_R2_0_I3
  /\ Inv5742_3d78_R2_0_I3
  /\ Inv11_3838_R8_0_I2
  /\ Inv61_df69_R8_0_I2
  /\ Inv1922_5e75_R2_0_I3
  /\ Inv4227_eecc_R10_0_I3
  /\ Inv2740_e784_R16_0_I3
  /\ Inv0_b3ba_R18_0_I0
  /\ Inv1_b58a_R20_0_I1
  /\ Inv350_b077_R20_1_I2
  /\ Inv40_180c_R24_0_I1
  /\ Inv6093_1c74_R18_1_I2
  /\ Inv103_c9b1_R21_1_I1
  /\ Inv80_b6ff_R2_0_I3
  /\ Inv140_f68c_R9_0_I1
  /\ Inv1028_6ea5_R8_0_I2
  /\ Inv24959_7f87_R1_1_I2
  /\ Inv5819_32cd_R1_1_I2
  /\ Inv4576_59b1_R1_1_I2
  /\ Inv4606_2f6b_R5_0_I2
  /\ Inv32498_2818_R11_0_I2
  /\ Inv3293_1a1e_R17_0_I3
  /\ Inv19_037d_R19_0_I1
  /\ Inv4521_3f08_R1_1_I2


\* mean in-degree: 1.7037037037037037
\* median in-degree: 2
\* max in-degree: 5
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == N \in Nat /\ Procs \subseteq Nat /\ IsFiniteSet(Procs)

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0
  \* (TypeOK,ncsAction)
  <1>1. TypeOK /\ TypeOK /\ ncsAction => TypeOK' BY DEF TypeOK,ncsAction,ncs,TypeOK,\prec
  \* (TypeOK,e1aAction)
  <1>2. TypeOK /\ TypeOK /\ e1aAction => TypeOK' BY DEF TypeOK,e1aAction,e1a,TypeOK,\prec
  \* (TypeOK,e1bAction)
  <1>3. TypeOK /\ TypeOK /\ e1bAction => TypeOK' BY DEF TypeOK,e1bAction,e1b,TypeOK,\prec
  \* (TypeOK,e2aAction)
  <1>4. TypeOK /\ TypeOK /\ e2aAction => TypeOK' BY DEF TypeOK,e2aAction,e2a,TypeOK,\prec,Procs
  \* (TypeOK,e2bAction)
  <1>5. TypeOK /\ TypeOK /\ e2bAction => TypeOK' BY DEF TypeOK,e2bAction,e2b,TypeOK,\prec
  \* (TypeOK,e3aAction)
  <1>6. TypeOK /\ TypeOK /\ e3aAction => TypeOK' BY DEF TypeOK,e3aAction,e3a,TypeOK,\prec
  \* (TypeOK,e3bAction)
  <1>7. TypeOK /\ TypeOK /\ e3bAction => TypeOK' BY DEF TypeOK,e3bAction,e3b,TypeOK,\prec,\prec
  \* (TypeOK,e4aAction)
  <1>8. TypeOK /\ TypeOK /\ e4aAction => TypeOK' BY DEF TypeOK,e4aAction,e4a,TypeOK,\prec
  \* (TypeOK,e4bAction)
  <1>9. TypeOK /\ TypeOK /\ e4bAction => TypeOK' BY DEF TypeOK,e4bAction,e4b,TypeOK,\prec,\prec
  \* (TypeOK,w1aAction)
  <1>10. TypeOK /\ TypeOK /\ w1aAction => TypeOK' BY DEF TypeOK,w1aAction,w1a,TypeOK,\prec,\prec
  \* (TypeOK,w1bAction)
  <1>11. TypeOK /\ TypeOK /\ w1bAction => TypeOK' BY DEF TypeOK,w1bAction,w1b,TypeOK,\prec,\prec
  \* (TypeOK,w2Action)
  <1>12. TypeOK /\ TypeOK /\ w2Action => TypeOK' BY DEF TypeOK,w2Action,w2,TypeOK,\prec,\prec
  \* (TypeOK,csAction)
  <1>13. TypeOK /\ TypeOK /\ csAction => TypeOK' BY DEF TypeOK,csAction,cs,TypeOK,\prec
  \* (TypeOK,exitAction)
  <1>14. TypeOK /\ TypeOK /\ exitAction => TypeOK' BY DEF TypeOK,exitAction,exit,TypeOK,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv4690_2f61_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0
  \* (Safety,ncsAction)
  <1>1. TypeOK /\ Safety /\ ncsAction => Safety' BY DEF TypeOK,ncsAction,ncs,Safety,\prec,H_MutualExclusion
  \* (Safety,e1aAction)
  <1>2. TypeOK /\ Safety /\ e1aAction => Safety' BY DEF TypeOK,e1aAction,e1a,Safety,\prec,H_MutualExclusion
  \* (Safety,e1bAction)
  <1>3. TypeOK /\ Safety /\ e1bAction => Safety' BY DEF TypeOK,e1bAction,e1b,Safety,\prec,H_MutualExclusion
  \* (Safety,e2aAction)
  <1>4. TypeOK /\ Safety /\ e2aAction => Safety' BY DEF TypeOK,e2aAction,e2a,Safety,\prec,Procs,H_MutualExclusion
  \* (Safety,e2bAction)
  <1>5. TypeOK /\ Safety /\ e2bAction => Safety' BY DEF TypeOK,e2bAction,e2b,Safety,\prec,H_MutualExclusion
  \* (Safety,e3aAction)
  <1>6. TypeOK /\ Safety /\ e3aAction => Safety' BY DEF TypeOK,e3aAction,e3a,Safety,\prec,H_MutualExclusion
  \* (Safety,e3bAction)
  <1>7. TypeOK /\ Safety /\ e3bAction => Safety' BY DEF TypeOK,e3bAction,e3b,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,e4aAction)
  <1>8. TypeOK /\ Safety /\ e4aAction => Safety' BY DEF TypeOK,e4aAction,e4a,Safety,\prec,H_MutualExclusion
  \* (Safety,e4bAction)
  <1>9. TypeOK /\ Safety /\ e4bAction => Safety' BY DEF TypeOK,e4bAction,e4b,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,w1aAction)
  <1>10. TypeOK /\ Safety /\ w1aAction => Safety' BY DEF TypeOK,w1aAction,w1a,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,w1bAction)
  <1>11. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ Safety /\ w1bAction => Safety' BY DEF TypeOK,Inv4690_2f61_R0_0_I2,w1bAction,w1b,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,w2Action)
  <1>12. TypeOK /\ Safety /\ w2Action => Safety' BY DEF TypeOK,w2Action,w2,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,csAction)
  <1>13. TypeOK /\ Safety /\ csAction => Safety' BY DEF TypeOK,csAction,cs,Safety,\prec,H_MutualExclusion
  \* (Safety,exitAction)
  <1>14. TypeOK /\ Safety /\ exitAction => Safety' BY DEF TypeOK,exitAction,exit,Safety,\prec,H_MutualExclusion
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4690_2f61_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv4520_48f3_R1_0_I2 /\ Inv24959_7f87_R1_1_I2 /\ Inv5819_32cd_R1_1_I2 /\ Inv4576_59b1_R1_1_I2 /\ Inv4521_3f08_R1_1_I2 /\ Inv4690_2f61_R0_0_I2 /\ Next => Inv4690_2f61_R0_0_I2'
  <1>. USE A0
  \* (Inv4690_2f61_R0_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ ncsAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e1aAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e1bAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e2aAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv4690_2f61_R0_0_I2,\prec,Procs
  \* (Inv4690_2f61_R0_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e2bAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e3aAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e3bAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (Inv4690_2f61_R0_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e4aAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ e4bAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (Inv4690_2f61_R0_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ w1aAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (Inv4690_2f61_R0_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ Inv4690_2f61_R0_0_I2 /\ w1bAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,Inv4520_48f3_R1_0_I2,w1bAction,w1b,Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (Inv4690_2f61_R0_0_I2,w2Action)
  <1>12. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ Inv5819_32cd_R1_1_I2 /\ Inv4576_59b1_R1_1_I2 /\ Inv4521_3f08_R1_1_I2 /\ Inv4690_2f61_R0_0_I2 /\ w2Action => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,Inv24959_7f87_R1_1_I2,Inv5819_32cd_R1_1_I2,Inv4576_59b1_R1_1_I2,Inv4521_3f08_R1_1_I2,w2Action,w2,Inv4690_2f61_R0_0_I2,\prec,\prec
  \* (Inv4690_2f61_R0_0_I2,csAction)
  <1>13. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ csAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,csAction,cs,Inv4690_2f61_R0_0_I2,\prec
  \* (Inv4690_2f61_R0_0_I2,exitAction)
  <1>14. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ exitAction => Inv4690_2f61_R0_0_I2' BY DEF TypeOK,exitAction,exit,Inv4690_2f61_R0_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4520_48f3_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv10_8778_R2_0_I3 /\ Inv5742_3d78_R2_0_I3 /\ Inv80_b6ff_R2_0_I3 /\ Inv1922_5e75_R2_0_I3 /\ Inv4520_48f3_R1_0_I2 /\ Next => Inv4520_48f3_R1_0_I2'
  <1>. USE A0
  \* (Inv4520_48f3_R1_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ ncsAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e1aAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e1bAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e2aAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv4520_48f3_R1_0_I2,\prec,Procs
  \* (Inv4520_48f3_R1_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e2bAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e3aAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e3bAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (Inv4520_48f3_R1_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e4aAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ e4bAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (Inv4520_48f3_R1_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ w1aAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (Inv4520_48f3_R1_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ w1bAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,w1bAction,w1b,Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (Inv4520_48f3_R1_0_I2,w2Action)
  <1>12. TypeOK /\ Inv10_8778_R2_0_I3 /\ Inv5742_3d78_R2_0_I3 /\ Inv80_b6ff_R2_0_I3 /\ Inv1922_5e75_R2_0_I3 /\ Inv4520_48f3_R1_0_I2 /\ w2Action => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,Inv10_8778_R2_0_I3,Inv5742_3d78_R2_0_I3,Inv80_b6ff_R2_0_I3,Inv1922_5e75_R2_0_I3,w2Action,w2,Inv4520_48f3_R1_0_I2,\prec,\prec
  \* (Inv4520_48f3_R1_0_I2,csAction)
  <1>13. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ csAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,csAction,cs,Inv4520_48f3_R1_0_I2,\prec
  \* (Inv4520_48f3_R1_0_I2,exitAction)
  <1>14. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ exitAction => Inv4520_48f3_R1_0_I2' BY DEF TypeOK,exitAction,exit,Inv4520_48f3_R1_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv10_8778_R2_0_I3
THEOREM L_4 == TypeOK /\ Inv10_8778_R2_0_I3 /\ Next => Inv10_8778_R2_0_I3'
  <1>. USE A0
  \* (Inv10_8778_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv10_8778_R2_0_I3 /\ ncsAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv10_8778_R2_0_I3 /\ e1aAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv10_8778_R2_0_I3 /\ e1bAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv10_8778_R2_0_I3 /\ e2aAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv10_8778_R2_0_I3,\prec,Procs
  \* (Inv10_8778_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv10_8778_R2_0_I3 /\ e2bAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv10_8778_R2_0_I3 /\ e3aAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv10_8778_R2_0_I3 /\ e3bAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv10_8778_R2_0_I3,\prec,\prec
  \* (Inv10_8778_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv10_8778_R2_0_I3 /\ e4aAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv10_8778_R2_0_I3 /\ e4bAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv10_8778_R2_0_I3,\prec,\prec
  \* (Inv10_8778_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv10_8778_R2_0_I3 /\ w1aAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv10_8778_R2_0_I3,\prec,\prec
  \* (Inv10_8778_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv10_8778_R2_0_I3 /\ w1bAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv10_8778_R2_0_I3,\prec,\prec
  \* (Inv10_8778_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv10_8778_R2_0_I3 /\ w2Action => Inv10_8778_R2_0_I3' BY DEF TypeOK,w2Action,w2,Inv10_8778_R2_0_I3,\prec,\prec
  \* (Inv10_8778_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv10_8778_R2_0_I3 /\ csAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,csAction,cs,Inv10_8778_R2_0_I3,\prec
  \* (Inv10_8778_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv10_8778_R2_0_I3 /\ exitAction => Inv10_8778_R2_0_I3' BY DEF TypeOK,exitAction,exit,Inv10_8778_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv5742_3d78_R2_0_I3
THEOREM L_5 == TypeOK /\ Inv11_3838_R8_0_I2 /\ Inv61_df69_R8_0_I2 /\ Inv1922_5e75_R2_0_I3 /\ Inv1028_6ea5_R8_0_I2 /\ Inv5742_3d78_R2_0_I3 /\ Next => Inv5742_3d78_R2_0_I3'
  <1>. USE A0
  \* (Inv5742_3d78_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ ncsAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e1aAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e1bAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e2aAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv5742_3d78_R2_0_I3,\prec,Procs
  \* (Inv5742_3d78_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e2bAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e3aAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e3bAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (Inv5742_3d78_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e4aAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ e4bAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (Inv5742_3d78_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv11_3838_R8_0_I2 /\ Inv61_df69_R8_0_I2 /\ Inv1922_5e75_R2_0_I3 /\ Inv1028_6ea5_R8_0_I2 /\ Inv5742_3d78_R2_0_I3 /\ w1aAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,Inv11_3838_R8_0_I2,Inv61_df69_R8_0_I2,Inv1922_5e75_R2_0_I3,Inv1028_6ea5_R8_0_I2,w1aAction,w1a,Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (Inv5742_3d78_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ w1bAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (Inv5742_3d78_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ w2Action => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,w2Action,w2,Inv5742_3d78_R2_0_I3,\prec,\prec
  \* (Inv5742_3d78_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ csAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,csAction,cs,Inv5742_3d78_R2_0_I3,\prec
  \* (Inv5742_3d78_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv5742_3d78_R2_0_I3 /\ exitAction => Inv5742_3d78_R2_0_I3' BY DEF TypeOK,exitAction,exit,Inv5742_3d78_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv11_3838_R8_0_I2
THEOREM L_6 == TypeOK /\ Inv11_3838_R8_0_I2 /\ Next => Inv11_3838_R8_0_I2'
  <1>. USE A0
  \* (Inv11_3838_R8_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv11_3838_R8_0_I2 /\ ncsAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv11_3838_R8_0_I2 /\ e1aAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv11_3838_R8_0_I2 /\ e1bAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv11_3838_R8_0_I2 /\ e2aAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv11_3838_R8_0_I2,\prec,Procs
  \* (Inv11_3838_R8_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv11_3838_R8_0_I2 /\ e2bAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv11_3838_R8_0_I2 /\ e3aAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv11_3838_R8_0_I2 /\ e3bAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv11_3838_R8_0_I2,\prec,\prec
  \* (Inv11_3838_R8_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv11_3838_R8_0_I2 /\ e4aAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv11_3838_R8_0_I2 /\ e4bAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv11_3838_R8_0_I2,\prec,\prec
  \* (Inv11_3838_R8_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv11_3838_R8_0_I2 /\ w1aAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv11_3838_R8_0_I2,\prec,\prec
  \* (Inv11_3838_R8_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv11_3838_R8_0_I2 /\ w1bAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,w1bAction,w1b,Inv11_3838_R8_0_I2,\prec,\prec
  \* (Inv11_3838_R8_0_I2,w2Action)
  <1>12. TypeOK /\ Inv11_3838_R8_0_I2 /\ w2Action => Inv11_3838_R8_0_I2' BY DEF TypeOK,w2Action,w2,Inv11_3838_R8_0_I2,\prec,\prec
  \* (Inv11_3838_R8_0_I2,csAction)
  <1>13. TypeOK /\ Inv11_3838_R8_0_I2 /\ csAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,csAction,cs,Inv11_3838_R8_0_I2,\prec
  \* (Inv11_3838_R8_0_I2,exitAction)
  <1>14. TypeOK /\ Inv11_3838_R8_0_I2 /\ exitAction => Inv11_3838_R8_0_I2' BY DEF TypeOK,exitAction,exit,Inv11_3838_R8_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv61_df69_R8_0_I2
THEOREM L_7 == TypeOK /\ Inv61_df69_R8_0_I2 /\ Next => Inv61_df69_R8_0_I2'
  <1>. USE A0
  \* (Inv61_df69_R8_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv61_df69_R8_0_I2 /\ ncsAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv61_df69_R8_0_I2 /\ e1aAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv61_df69_R8_0_I2 /\ e1bAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv61_df69_R8_0_I2 /\ e2aAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv61_df69_R8_0_I2,\prec,Procs
  \* (Inv61_df69_R8_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv61_df69_R8_0_I2 /\ e2bAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv61_df69_R8_0_I2 /\ e3aAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv61_df69_R8_0_I2 /\ e3bAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv61_df69_R8_0_I2,\prec,\prec
  \* (Inv61_df69_R8_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv61_df69_R8_0_I2 /\ e4aAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv61_df69_R8_0_I2 /\ e4bAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv61_df69_R8_0_I2,\prec,\prec
  \* (Inv61_df69_R8_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv61_df69_R8_0_I2 /\ w1aAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv61_df69_R8_0_I2,\prec,\prec
  \* (Inv61_df69_R8_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv61_df69_R8_0_I2 /\ w1bAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,w1bAction,w1b,Inv61_df69_R8_0_I2,\prec,\prec
  \* (Inv61_df69_R8_0_I2,w2Action)
  <1>12. TypeOK /\ Inv61_df69_R8_0_I2 /\ w2Action => Inv61_df69_R8_0_I2' BY DEF TypeOK,w2Action,w2,Inv61_df69_R8_0_I2,\prec,\prec
  \* (Inv61_df69_R8_0_I2,csAction)
  <1>13. TypeOK /\ Inv61_df69_R8_0_I2 /\ csAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,csAction,cs,Inv61_df69_R8_0_I2,\prec
  \* (Inv61_df69_R8_0_I2,exitAction)
  <1>14. TypeOK /\ Inv61_df69_R8_0_I2 /\ exitAction => Inv61_df69_R8_0_I2' BY DEF TypeOK,exitAction,exit,Inv61_df69_R8_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1922_5e75_R2_0_I3
THEOREM L_8 == TypeOK /\ Inv4227_eecc_R10_0_I3 /\ Inv80_b6ff_R2_0_I3 /\ Inv4227_eecc_R10_0_I3 /\ Inv1922_5e75_R2_0_I3 /\ Next => Inv1922_5e75_R2_0_I3'
  <1>. USE A0
  \* (Inv1922_5e75_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ ncsAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e1aAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e1bAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e2aAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv1922_5e75_R2_0_I3,\prec,Procs
  \* (Inv1922_5e75_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e2bAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e3aAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e3bAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (Inv1922_5e75_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ e4aAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ Inv1922_5e75_R2_0_I3 /\ e4bAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,Inv4227_eecc_R10_0_I3,e4bAction,e4b,Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (Inv1922_5e75_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ w1aAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (Inv1922_5e75_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ w1bAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (Inv1922_5e75_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ Inv4227_eecc_R10_0_I3 /\ Inv1922_5e75_R2_0_I3 /\ w2Action => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,Inv80_b6ff_R2_0_I3,Inv4227_eecc_R10_0_I3,w2Action,w2,Inv1922_5e75_R2_0_I3,\prec,\prec
  \* (Inv1922_5e75_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ csAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,csAction,cs,Inv1922_5e75_R2_0_I3,\prec
  \* (Inv1922_5e75_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ exitAction => Inv1922_5e75_R2_0_I3' BY DEF TypeOK,exitAction,exit,Inv1922_5e75_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4227_eecc_R10_0_I3
THEOREM L_9 == TypeOK /\ Inv2740_e784_R16_0_I3 /\ Inv11_3838_R8_0_I2 /\ Inv80_b6ff_R2_0_I3 /\ Inv140_f68c_R9_0_I1 /\ Inv4227_eecc_R10_0_I3 /\ Next => Inv4227_eecc_R10_0_I3'
  <1>. USE A0
  \* (Inv4227_eecc_R10_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ ncsAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e1aAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e1bAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e2aAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv4227_eecc_R10_0_I3,\prec,Procs
  \* (Inv4227_eecc_R10_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e2bAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e3aAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv2740_e784_R16_0_I3 /\ Inv4227_eecc_R10_0_I3 /\ e3bAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,Inv2740_e784_R16_0_I3,e3bAction,e3b,Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (Inv4227_eecc_R10_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e4aAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ e4bAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (Inv4227_eecc_R10_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ w1aAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (Inv4227_eecc_R10_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ w1bAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (Inv4227_eecc_R10_0_I3,w2Action)
  <1>12. TypeOK /\ Inv11_3838_R8_0_I2 /\ Inv80_b6ff_R2_0_I3 /\ Inv140_f68c_R9_0_I1 /\ Inv4227_eecc_R10_0_I3 /\ w2Action => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,Inv11_3838_R8_0_I2,Inv80_b6ff_R2_0_I3,Inv140_f68c_R9_0_I1,w2Action,w2,Inv4227_eecc_R10_0_I3,\prec,\prec
  \* (Inv4227_eecc_R10_0_I3,csAction)
  <1>13. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ csAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,csAction,cs,Inv4227_eecc_R10_0_I3,\prec
  \* (Inv4227_eecc_R10_0_I3,exitAction)
  <1>14. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ exitAction => Inv4227_eecc_R10_0_I3' BY DEF TypeOK,exitAction,exit,Inv4227_eecc_R10_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2740_e784_R16_0_I3
THEOREM L_10 == TypeOK /\ Inv0_b3ba_R18_0_I0 /\ Inv6093_1c74_R18_1_I2 /\ Inv2740_e784_R16_0_I3 /\ Next => Inv2740_e784_R16_0_I3'
  <1>. USE A0
  \* (Inv2740_e784_R16_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv2740_e784_R16_0_I3 /\ ncsAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e1aAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e1bAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e2aAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv2740_e784_R16_0_I3,\prec,Procs
  \* (Inv2740_e784_R16_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ Inv2740_e784_R16_0_I3 /\ e2bAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,Inv0_b3ba_R18_0_I0,e2bAction,e2b,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e3aAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e3bAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv2740_e784_R16_0_I3,\prec,\prec
  \* (Inv2740_e784_R16_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e4aAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv2740_e784_R16_0_I3 /\ e4bAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv2740_e784_R16_0_I3,\prec,\prec
  \* (Inv2740_e784_R16_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv2740_e784_R16_0_I3 /\ w1aAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv2740_e784_R16_0_I3,\prec,\prec
  \* (Inv2740_e784_R16_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv2740_e784_R16_0_I3 /\ w1bAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv2740_e784_R16_0_I3,\prec,\prec
  \* (Inv2740_e784_R16_0_I3,w2Action)
  <1>12. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ Inv2740_e784_R16_0_I3 /\ w2Action => Inv2740_e784_R16_0_I3' BY DEF TypeOK,Inv6093_1c74_R18_1_I2,w2Action,w2,Inv2740_e784_R16_0_I3,\prec,\prec
  \* (Inv2740_e784_R16_0_I3,csAction)
  <1>13. TypeOK /\ Inv2740_e784_R16_0_I3 /\ csAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,csAction,cs,Inv2740_e784_R16_0_I3,\prec
  \* (Inv2740_e784_R16_0_I3,exitAction)
  <1>14. TypeOK /\ Inv2740_e784_R16_0_I3 /\ exitAction => Inv2740_e784_R16_0_I3' BY DEF TypeOK,exitAction,exit,Inv2740_e784_R16_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv0_b3ba_R18_0_I0
THEOREM L_11 == TypeOK /\ Inv1_b58a_R20_0_I1 /\ Inv350_b077_R20_1_I2 /\ Inv0_b3ba_R18_0_I0 /\ Next => Inv0_b3ba_R18_0_I0'
  <1>. USE A0
  \* (Inv0_b3ba_R18_0_I0,ncsAction)
  <1>1. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ ncsAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,ncsAction,ncs,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,e1aAction)
  <1>2. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e1aAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e1aAction,e1a,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,e1bAction)
  <1>3. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e1bAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e1bAction,e1b,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,e2aAction)
  <1>4. TypeOK /\ Inv1_b58a_R20_0_I1 /\ Inv0_b3ba_R18_0_I0 /\ e2aAction => Inv0_b3ba_R18_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1_b58a_R20_0_I1,
                        Inv0_b3ba_R18_0_I0,
                        TRUE,
                        NEW self \in Procs,
                        pc[self] = "e2",
                        unchecked[self] # {},
                        NEW i \in unchecked[self],
                        /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                        /\ IF num[i] > max[self]
                            THEN /\ max' = [max EXCEPT ![self] = num[i]]
                            ELSE /\ max' = max,
                        pc' = [pc EXCEPT ![self] = "e2"],
                        UNCHANGED << num, flag, nxt >>,
                        NEW VARI \in Procs',
                        NEW VARJ \in Procs'
                 PROVE  ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))'
      BY DEF Inv0_b3ba_R18_0_I0, e2a, e2aAction
    <2> QED
      BY SMTT(60) DEF TypeOK,Inv1_b58a_R20_0_I1,e2aAction,e2a,Inv0_b3ba_R18_0_I0,\prec,Procs
  \* (Inv0_b3ba_R18_0_I0,e2bAction)
  <1>5. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e2bAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e2bAction,e2b,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,e3aAction)
  <1>6. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e3aAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e3aAction,e3a,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,e3bAction)
  <1>7. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e3bAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e3bAction,e3b,Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (Inv0_b3ba_R18_0_I0,e4aAction)
  <1>8. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e4aAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e4aAction,e4a,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,e4bAction)
  <1>9. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ e4bAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,e4bAction,e4b,Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (Inv0_b3ba_R18_0_I0,w1aAction)
  <1>10. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ w1aAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,w1aAction,w1a,Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (Inv0_b3ba_R18_0_I0,w1bAction)
  <1>11. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ w1bAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,w1bAction,w1b,Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (Inv0_b3ba_R18_0_I0,w2Action)
  <1>12. TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv0_b3ba_R18_0_I0 /\ w2Action => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,Inv350_b077_R20_1_I2,w2Action,w2,Inv0_b3ba_R18_0_I0,\prec,\prec
  \* (Inv0_b3ba_R18_0_I0,csAction)
  <1>13. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ csAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,csAction,cs,Inv0_b3ba_R18_0_I0,\prec
  \* (Inv0_b3ba_R18_0_I0,exitAction)
  <1>14. TypeOK /\ Inv0_b3ba_R18_0_I0 /\ exitAction => Inv0_b3ba_R18_0_I0' BY DEF TypeOK,exitAction,exit,Inv0_b3ba_R18_0_I0,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1_b58a_R20_0_I1
THEOREM L_12 == TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv1_b58a_R20_0_I1 /\ Next => Inv1_b58a_R20_0_I1'
  <1>. USE A0
  \* (Inv1_b58a_R20_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1_b58a_R20_0_I1 /\ ncsAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,ncsAction,ncs,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e1aAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e1aAction,e1a,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e1bAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e1bAction,e1b,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e2aAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e2aAction,e2a,Inv1_b58a_R20_0_I1,\prec,Procs
  \* (Inv1_b58a_R20_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e2bAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e2bAction,e2b,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e3aAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e3aAction,e3a,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e3bAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e3bAction,e3b,Inv1_b58a_R20_0_I1,\prec,\prec
  \* (Inv1_b58a_R20_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e4aAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e4aAction,e4a,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv1_b58a_R20_0_I1 /\ e4bAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,e4bAction,e4b,Inv1_b58a_R20_0_I1,\prec,\prec
  \* (Inv1_b58a_R20_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv1_b58a_R20_0_I1 /\ w1aAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,w1aAction,w1a,Inv1_b58a_R20_0_I1,\prec,\prec
  \* (Inv1_b58a_R20_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv1_b58a_R20_0_I1 /\ w1bAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,w1bAction,w1b,Inv1_b58a_R20_0_I1,\prec,\prec
  \* (Inv1_b58a_R20_0_I1,w2Action)
  <1>12. TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv1_b58a_R20_0_I1 /\ w2Action => Inv1_b58a_R20_0_I1' BY DEF TypeOK,Inv350_b077_R20_1_I2,w2Action,w2,Inv1_b58a_R20_0_I1,\prec,\prec
  \* (Inv1_b58a_R20_0_I1,csAction)
  <1>13. TypeOK /\ Inv1_b58a_R20_0_I1 /\ csAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,csAction,cs,Inv1_b58a_R20_0_I1,\prec
  \* (Inv1_b58a_R20_0_I1,exitAction)
  <1>14. TypeOK /\ Inv1_b58a_R20_0_I1 /\ exitAction => Inv1_b58a_R20_0_I1' BY DEF TypeOK,exitAction,exit,Inv1_b58a_R20_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv350_b077_R20_1_I2
THEOREM L_13 == TypeOK /\ Inv40_180c_R24_0_I1 /\ Inv350_b077_R20_1_I2 /\ Next => Inv350_b077_R20_1_I2'
  <1>. USE A0
  \* (Inv350_b077_R20_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv350_b077_R20_1_I2 /\ ncsAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv350_b077_R20_1_I2 /\ e1aAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv350_b077_R20_1_I2 /\ e1bAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv350_b077_R20_1_I2 /\ e2aAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv350_b077_R20_1_I2,\prec,Procs
  \* (Inv350_b077_R20_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv350_b077_R20_1_I2 /\ e2bAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv350_b077_R20_1_I2 /\ e3aAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv350_b077_R20_1_I2 /\ e3bAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv350_b077_R20_1_I2,\prec,\prec
  \* (Inv350_b077_R20_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv350_b077_R20_1_I2 /\ e4aAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv350_b077_R20_1_I2 /\ e4bAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv350_b077_R20_1_I2,\prec,\prec
  \* (Inv350_b077_R20_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv40_180c_R24_0_I1 /\ Inv350_b077_R20_1_I2 /\ w1aAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,Inv40_180c_R24_0_I1,w1aAction,w1a,Inv350_b077_R20_1_I2,\prec,\prec
  \* (Inv350_b077_R20_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv350_b077_R20_1_I2 /\ w1bAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,w1bAction,w1b,Inv350_b077_R20_1_I2,\prec,\prec
  \* (Inv350_b077_R20_1_I2,w2Action)
  <1>12. TypeOK /\ Inv350_b077_R20_1_I2 /\ w2Action => Inv350_b077_R20_1_I2' BY DEF TypeOK,w2Action,w2,Inv350_b077_R20_1_I2,\prec,\prec
  \* (Inv350_b077_R20_1_I2,csAction)
  <1>13. TypeOK /\ Inv350_b077_R20_1_I2 /\ csAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,csAction,cs,Inv350_b077_R20_1_I2,\prec
  \* (Inv350_b077_R20_1_I2,exitAction)
  <1>14. TypeOK /\ Inv350_b077_R20_1_I2 /\ exitAction => Inv350_b077_R20_1_I2' BY DEF TypeOK,exitAction,exit,Inv350_b077_R20_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv40_180c_R24_0_I1
THEOREM L_14 == TypeOK /\ Inv40_180c_R24_0_I1 /\ Next => Inv40_180c_R24_0_I1'
  <1>. USE A0
  \* (Inv40_180c_R24_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv40_180c_R24_0_I1 /\ ncsAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,ncsAction,ncs,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv40_180c_R24_0_I1 /\ e1aAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e1aAction,e1a,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv40_180c_R24_0_I1 /\ e1bAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e1bAction,e1b,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv40_180c_R24_0_I1 /\ e2aAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e2aAction,e2a,Inv40_180c_R24_0_I1,\prec,Procs
  \* (Inv40_180c_R24_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv40_180c_R24_0_I1 /\ e2bAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e2bAction,e2b,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv40_180c_R24_0_I1 /\ e3aAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e3aAction,e3a,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv40_180c_R24_0_I1 /\ e3bAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e3bAction,e3b,Inv40_180c_R24_0_I1,\prec,\prec
  \* (Inv40_180c_R24_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv40_180c_R24_0_I1 /\ e4aAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e4aAction,e4a,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv40_180c_R24_0_I1 /\ e4bAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,e4bAction,e4b,Inv40_180c_R24_0_I1,\prec,\prec
  \* (Inv40_180c_R24_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv40_180c_R24_0_I1 /\ w1aAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,w1aAction,w1a,Inv40_180c_R24_0_I1,\prec,\prec
  \* (Inv40_180c_R24_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv40_180c_R24_0_I1 /\ w1bAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,w1bAction,w1b,Inv40_180c_R24_0_I1,\prec,\prec
  \* (Inv40_180c_R24_0_I1,w2Action)
  <1>12. TypeOK /\ Inv40_180c_R24_0_I1 /\ w2Action => Inv40_180c_R24_0_I1' BY DEF TypeOK,w2Action,w2,Inv40_180c_R24_0_I1,\prec,\prec
  \* (Inv40_180c_R24_0_I1,csAction)
  <1>13. TypeOK /\ Inv40_180c_R24_0_I1 /\ csAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,csAction,cs,Inv40_180c_R24_0_I1,\prec
  \* (Inv40_180c_R24_0_I1,exitAction)
  <1>14. TypeOK /\ Inv40_180c_R24_0_I1 /\ exitAction => Inv40_180c_R24_0_I1' BY DEF TypeOK,exitAction,exit,Inv40_180c_R24_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv6093_1c74_R18_1_I2
THEOREM L_15 == TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv103_c9b1_R21_1_I1 /\ Inv6093_1c74_R18_1_I2 /\ Next => Inv6093_1c74_R18_1_I2'
  <1>. USE A0
  \* (Inv6093_1c74_R18_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ ncsAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e1aAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e1bAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e2aAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv6093_1c74_R18_1_I2,\prec,Procs
  \* (Inv6093_1c74_R18_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv6093_1c74_R18_1_I2 /\ e2bAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,Inv350_b077_R20_1_I2,e2bAction,e2b,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e3aAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e3bAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (Inv6093_1c74_R18_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e4aAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ e4bAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (Inv6093_1c74_R18_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ Inv6093_1c74_R18_1_I2 /\ w1aAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,Inv103_c9b1_R21_1_I1,w1aAction,w1a,Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (Inv6093_1c74_R18_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ w1bAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,w1bAction,w1b,Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (Inv6093_1c74_R18_1_I2,w2Action)
  <1>12. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ w2Action => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,w2Action,w2,Inv6093_1c74_R18_1_I2,\prec,\prec
  \* (Inv6093_1c74_R18_1_I2,csAction)
  <1>13. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ csAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,csAction,cs,Inv6093_1c74_R18_1_I2,\prec
  \* (Inv6093_1c74_R18_1_I2,exitAction)
  <1>14. TypeOK /\ Inv6093_1c74_R18_1_I2 /\ exitAction => Inv6093_1c74_R18_1_I2' BY DEF TypeOK,exitAction,exit,Inv6093_1c74_R18_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv103_c9b1_R21_1_I1
THEOREM L_16 == TypeOK /\ Inv40_180c_R24_0_I1 /\ Inv103_c9b1_R21_1_I1 /\ Next => Inv103_c9b1_R21_1_I1'
  <1>. USE A0
  \* (Inv103_c9b1_R21_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ ncsAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,ncsAction,ncs,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,e1aAction)
  <1>2. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e1aAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e1aAction,e1a,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,e1bAction)
  <1>3. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e1bAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e1bAction,e1b,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,e2aAction)
  <1>4. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e2aAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e2aAction,e2a,Inv103_c9b1_R21_1_I1,\prec,Procs
  \* (Inv103_c9b1_R21_1_I1,e2bAction)
  <1>5. TypeOK /\ Inv40_180c_R24_0_I1 /\ Inv103_c9b1_R21_1_I1 /\ e2bAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,Inv40_180c_R24_0_I1,e2bAction,e2b,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,e3aAction)
  <1>6. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e3aAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e3aAction,e3a,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,e3bAction)
  <1>7. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e3bAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e3bAction,e3b,Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (Inv103_c9b1_R21_1_I1,e4aAction)
  <1>8. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e4aAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e4aAction,e4a,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,e4bAction)
  <1>9. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ e4bAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,e4bAction,e4b,Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (Inv103_c9b1_R21_1_I1,w1aAction)
  <1>10. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ w1aAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,w1aAction,w1a,Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (Inv103_c9b1_R21_1_I1,w1bAction)
  <1>11. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ w1bAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,w1bAction,w1b,Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (Inv103_c9b1_R21_1_I1,w2Action)
  <1>12. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ w2Action => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,w2Action,w2,Inv103_c9b1_R21_1_I1,\prec,\prec
  \* (Inv103_c9b1_R21_1_I1,csAction)
  <1>13. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ csAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,csAction,cs,Inv103_c9b1_R21_1_I1,\prec
  \* (Inv103_c9b1_R21_1_I1,exitAction)
  <1>14. TypeOK /\ Inv103_c9b1_R21_1_I1 /\ exitAction => Inv103_c9b1_R21_1_I1' BY DEF TypeOK,exitAction,exit,Inv103_c9b1_R21_1_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv80_b6ff_R2_0_I3
THEOREM L_17 == TypeOK /\ Inv140_f68c_R9_0_I1 /\ Inv80_b6ff_R2_0_I3 /\ Next => Inv80_b6ff_R2_0_I3'
  <1>. USE A0
  \* (Inv80_b6ff_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ ncsAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e1aAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e1bAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e2aAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv80_b6ff_R2_0_I3,\prec,Procs
  \* (Inv80_b6ff_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e2bAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e3aAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e3bAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (Inv80_b6ff_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ e4aAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv140_f68c_R9_0_I1 /\ Inv80_b6ff_R2_0_I3 /\ e4bAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,Inv140_f68c_R9_0_I1,e4bAction,e4b,Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (Inv80_b6ff_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ w1aAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (Inv80_b6ff_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ w1bAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (Inv80_b6ff_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ w2Action => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,w2Action,w2,Inv80_b6ff_R2_0_I3,\prec,\prec
  \* (Inv80_b6ff_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ csAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,csAction,cs,Inv80_b6ff_R2_0_I3,\prec
  \* (Inv80_b6ff_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ exitAction => Inv80_b6ff_R2_0_I3' BY DEF TypeOK,exitAction,exit,Inv80_b6ff_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv140_f68c_R9_0_I1
THEOREM L_18 == TypeOK /\ Inv140_f68c_R9_0_I1 /\ Next => Inv140_f68c_R9_0_I1'
  <1>. USE A0
  \* (Inv140_f68c_R9_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv140_f68c_R9_0_I1 /\ ncsAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,ncsAction,ncs,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e1aAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e1aAction,e1a,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e1bAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e1bAction,e1b,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e2aAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e2aAction,e2a,Inv140_f68c_R9_0_I1,\prec,Procs
  \* (Inv140_f68c_R9_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e2bAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e2bAction,e2b,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e3aAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e3aAction,e3a,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e3bAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e3bAction,e3b,Inv140_f68c_R9_0_I1,\prec,\prec
  \* (Inv140_f68c_R9_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e4aAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e4aAction,e4a,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv140_f68c_R9_0_I1 /\ e4bAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,e4bAction,e4b,Inv140_f68c_R9_0_I1,\prec,\prec
  \* (Inv140_f68c_R9_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv140_f68c_R9_0_I1 /\ w1aAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,w1aAction,w1a,Inv140_f68c_R9_0_I1,\prec,\prec
  \* (Inv140_f68c_R9_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv140_f68c_R9_0_I1 /\ w1bAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,w1bAction,w1b,Inv140_f68c_R9_0_I1,\prec,\prec
  \* (Inv140_f68c_R9_0_I1,w2Action)
  <1>12. TypeOK /\ Inv140_f68c_R9_0_I1 /\ w2Action => Inv140_f68c_R9_0_I1' BY DEF TypeOK,w2Action,w2,Inv140_f68c_R9_0_I1,\prec,\prec
  \* (Inv140_f68c_R9_0_I1,csAction)
  <1>13. TypeOK /\ Inv140_f68c_R9_0_I1 /\ csAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,csAction,cs,Inv140_f68c_R9_0_I1,\prec
  \* (Inv140_f68c_R9_0_I1,exitAction)
  <1>14. TypeOK /\ Inv140_f68c_R9_0_I1 /\ exitAction => Inv140_f68c_R9_0_I1' BY DEF TypeOK,exitAction,exit,Inv140_f68c_R9_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1028_6ea5_R8_0_I2
THEOREM L_19 == TypeOK /\ Inv4227_eecc_R10_0_I3 /\ Inv4227_eecc_R10_0_I3 /\ Inv80_b6ff_R2_0_I3 /\ Inv1028_6ea5_R8_0_I2 /\ Next => Inv1028_6ea5_R8_0_I2'
  <1>. USE A0
  \* (Inv1028_6ea5_R8_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ ncsAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e1aAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e1bAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e2aAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv1028_6ea5_R8_0_I2,\prec,Procs
  \* (Inv1028_6ea5_R8_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e2bAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e3aAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e3bAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (Inv1028_6ea5_R8_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ e4aAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ Inv1028_6ea5_R8_0_I2 /\ e4bAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,Inv4227_eecc_R10_0_I3,e4bAction,e4b,Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (Inv1028_6ea5_R8_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ w1aAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (Inv1028_6ea5_R8_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ w1bAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,w1bAction,w1b,Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (Inv1028_6ea5_R8_0_I2,w2Action)
  <1>12. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ Inv80_b6ff_R2_0_I3 /\ Inv1028_6ea5_R8_0_I2 /\ w2Action => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,Inv4227_eecc_R10_0_I3,Inv80_b6ff_R2_0_I3,w2Action,w2,Inv1028_6ea5_R8_0_I2,\prec,\prec
  \* (Inv1028_6ea5_R8_0_I2,csAction)
  <1>13. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ csAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,csAction,cs,Inv1028_6ea5_R8_0_I2,\prec
  \* (Inv1028_6ea5_R8_0_I2,exitAction)
  <1>14. TypeOK /\ Inv1028_6ea5_R8_0_I2 /\ exitAction => Inv1028_6ea5_R8_0_I2' BY DEF TypeOK,exitAction,exit,Inv1028_6ea5_R8_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv24959_7f87_R1_1_I2
THEOREM L_20 == TypeOK /\ Inv24959_7f87_R1_1_I2 /\ Next => Inv24959_7f87_R1_1_I2'
  <1>. USE A0
  \* (Inv24959_7f87_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ ncsAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e1aAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e1bAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e2aAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv24959_7f87_R1_1_I2,\prec,Procs
  \* (Inv24959_7f87_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e2bAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e3aAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e3bAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (Inv24959_7f87_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e4aAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ e4bAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (Inv24959_7f87_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ w1aAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (Inv24959_7f87_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ w1bAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,w1bAction,w1b,Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (Inv24959_7f87_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ w2Action => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv24959_7f87_R1_1_I2,\prec,\prec
  \* (Inv24959_7f87_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ csAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv24959_7f87_R1_1_I2,\prec
  \* (Inv24959_7f87_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv24959_7f87_R1_1_I2 /\ exitAction => Inv24959_7f87_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv24959_7f87_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv5819_32cd_R1_1_I2
THEOREM L_21 == TypeOK /\ Inv4690_2f61_R0_0_I2 /\ Inv4520_48f3_R1_0_I2 /\ Inv5819_32cd_R1_1_I2 /\ Next => Inv5819_32cd_R1_1_I2'
  <1>. USE A0
  \* (Inv5819_32cd_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ ncsAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e1aAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e1bAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e2aAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv5819_32cd_R1_1_I2,\prec,Procs
  \* (Inv5819_32cd_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e2bAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e3aAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e3bAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (Inv5819_32cd_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e4aAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ e4bAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (Inv5819_32cd_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv4690_2f61_R0_0_I2 /\ Inv5819_32cd_R1_1_I2 /\ w1aAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,Inv4690_2f61_R0_0_I2,w1aAction,w1a,Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (Inv5819_32cd_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv4520_48f3_R1_0_I2 /\ Inv5819_32cd_R1_1_I2 /\ w1bAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,Inv4520_48f3_R1_0_I2,w1bAction,w1b,Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (Inv5819_32cd_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ w2Action => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv5819_32cd_R1_1_I2,\prec,\prec
  \* (Inv5819_32cd_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ csAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv5819_32cd_R1_1_I2,\prec
  \* (Inv5819_32cd_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv5819_32cd_R1_1_I2 /\ exitAction => Inv5819_32cd_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv5819_32cd_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4576_59b1_R1_1_I2
THEOREM L_22 == TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ Inv1922_5e75_R2_0_I3 /\ Inv4576_59b1_R1_1_I2 /\ Next => Inv4576_59b1_R1_1_I2'
  <1>. USE A0
  \* (Inv4576_59b1_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ ncsAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e1aAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e1bAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e2aAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv4576_59b1_R1_1_I2,\prec,Procs
  \* (Inv4576_59b1_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e2bAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e3aAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e3bAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (Inv4576_59b1_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e4aAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ e4bAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (Inv4576_59b1_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ Inv4576_59b1_R1_1_I2 /\ w1aAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,Inv4606_2f6b_R5_0_I2,w1aAction,w1a,Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (Inv4576_59b1_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv1922_5e75_R2_0_I3 /\ Inv4576_59b1_R1_1_I2 /\ w1bAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,Inv1922_5e75_R2_0_I3,w1bAction,w1b,Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (Inv4576_59b1_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ w2Action => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv4576_59b1_R1_1_I2,\prec,\prec
  \* (Inv4576_59b1_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ csAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv4576_59b1_R1_1_I2,\prec
  \* (Inv4576_59b1_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv4576_59b1_R1_1_I2 /\ exitAction => Inv4576_59b1_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv4576_59b1_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4606_2f6b_R5_0_I2
THEOREM L_23 == TypeOK /\ Inv32498_2818_R11_0_I2 /\ Inv4227_eecc_R10_0_I3 /\ Inv4606_2f6b_R5_0_I2 /\ Next => Inv4606_2f6b_R5_0_I2'
  <1>. USE A0
  \* (Inv4606_2f6b_R5_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ ncsAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e1aAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e1bAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e2aAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv4606_2f6b_R5_0_I2,\prec,Procs
  \* (Inv4606_2f6b_R5_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e2bAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e3aAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv32498_2818_R11_0_I2 /\ Inv4606_2f6b_R5_0_I2 /\ e3bAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,Inv32498_2818_R11_0_I2,e3bAction,e3b,Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (Inv4606_2f6b_R5_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e4aAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ e4bAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (Inv4606_2f6b_R5_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ w1aAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (Inv4606_2f6b_R5_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv4227_eecc_R10_0_I3 /\ Inv4606_2f6b_R5_0_I2 /\ w1bAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,Inv4227_eecc_R10_0_I3,w1bAction,w1b,Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (Inv4606_2f6b_R5_0_I2,w2Action)
  <1>12. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ w2Action => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,w2Action,w2,Inv4606_2f6b_R5_0_I2,\prec,\prec
  \* (Inv4606_2f6b_R5_0_I2,csAction)
  <1>13. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ csAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,csAction,cs,Inv4606_2f6b_R5_0_I2,\prec
  \* (Inv4606_2f6b_R5_0_I2,exitAction)
  <1>14. TypeOK /\ Inv4606_2f6b_R5_0_I2 /\ exitAction => Inv4606_2f6b_R5_0_I2' BY DEF TypeOK,exitAction,exit,Inv4606_2f6b_R5_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv32498_2818_R11_0_I2
THEOREM L_24 == TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ Inv2740_e784_R16_0_I3 /\ Inv32498_2818_R11_0_I2 /\ Next => Inv32498_2818_R11_0_I2'
  <1>. USE A0
  \* (Inv32498_2818_R11_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv32498_2818_R11_0_I2 /\ ncsAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e1aAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e1bAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e2aAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv32498_2818_R11_0_I2,\prec,Procs
  \* (Inv32498_2818_R11_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ Inv32498_2818_R11_0_I2 /\ e2bAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,Inv3293_1a1e_R17_0_I3,e2bAction,e2b,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e3aAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e3bAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv32498_2818_R11_0_I2,\prec,\prec
  \* (Inv32498_2818_R11_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e4aAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv32498_2818_R11_0_I2 /\ e4bAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv32498_2818_R11_0_I2,\prec,\prec
  \* (Inv32498_2818_R11_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv32498_2818_R11_0_I2 /\ w1aAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv32498_2818_R11_0_I2,\prec,\prec
  \* (Inv32498_2818_R11_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv2740_e784_R16_0_I3 /\ Inv32498_2818_R11_0_I2 /\ w1bAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,Inv2740_e784_R16_0_I3,w1bAction,w1b,Inv32498_2818_R11_0_I2,\prec,\prec
  \* (Inv32498_2818_R11_0_I2,w2Action)
  <1>12. TypeOK /\ Inv32498_2818_R11_0_I2 /\ w2Action => Inv32498_2818_R11_0_I2' BY DEF TypeOK,w2Action,w2,Inv32498_2818_R11_0_I2,\prec,\prec
  \* (Inv32498_2818_R11_0_I2,csAction)
  <1>13. TypeOK /\ Inv32498_2818_R11_0_I2 /\ csAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,csAction,cs,Inv32498_2818_R11_0_I2,\prec
  \* (Inv32498_2818_R11_0_I2,exitAction)
  <1>14. TypeOK /\ Inv32498_2818_R11_0_I2 /\ exitAction => Inv32498_2818_R11_0_I2' BY DEF TypeOK,exitAction,exit,Inv32498_2818_R11_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv3293_1a1e_R17_0_I3
THEOREM L_25 == TypeOK /\ Inv19_037d_R19_0_I1 /\ Inv3293_1a1e_R17_0_I3 /\ Next => Inv3293_1a1e_R17_0_I3'
  <1>. USE A0
  \* (Inv3293_1a1e_R17_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ ncsAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e1aAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e1bAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e2aAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv3293_1a1e_R17_0_I3,\prec,Procs
  \* (Inv3293_1a1e_R17_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e2bAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e3aAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e3bAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (Inv3293_1a1e_R17_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e4aAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ e4bAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (Inv3293_1a1e_R17_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ w1aAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (Inv3293_1a1e_R17_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv19_037d_R19_0_I1 /\ Inv3293_1a1e_R17_0_I3 /\ w1bAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,Inv19_037d_R19_0_I1,w1bAction,w1b,Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (Inv3293_1a1e_R17_0_I3,w2Action)
  <1>12. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ w2Action => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,w2Action,w2,Inv3293_1a1e_R17_0_I3,\prec,\prec
  \* (Inv3293_1a1e_R17_0_I3,csAction)
  <1>13. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ csAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,csAction,cs,Inv3293_1a1e_R17_0_I3,\prec
  \* (Inv3293_1a1e_R17_0_I3,exitAction)
  <1>14. TypeOK /\ Inv3293_1a1e_R17_0_I3 /\ exitAction => Inv3293_1a1e_R17_0_I3' BY DEF TypeOK,exitAction,exit,Inv3293_1a1e_R17_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv19_037d_R19_0_I1
THEOREM L_26 == TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv1_b58a_R20_0_I1 /\ Inv19_037d_R19_0_I1 /\ Next => Inv19_037d_R19_0_I1'
  <1>. USE A0
  \* (Inv19_037d_R19_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv19_037d_R19_0_I1 /\ ncsAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,ncsAction,ncs,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv19_037d_R19_0_I1 /\ e1aAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e1aAction,e1a,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv19_037d_R19_0_I1 /\ e1bAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e1bAction,e1b,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv19_037d_R19_0_I1 /\ e2aAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e2aAction,e2a,Inv19_037d_R19_0_I1,\prec,Procs
  \* (Inv19_037d_R19_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv19_037d_R19_0_I1 /\ e2bAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e2bAction,e2b,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv19_037d_R19_0_I1 /\ e3aAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e3aAction,e3a,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv19_037d_R19_0_I1 /\ e3bAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e3bAction,e3b,Inv19_037d_R19_0_I1,\prec,\prec
  \* (Inv19_037d_R19_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv19_037d_R19_0_I1 /\ e4aAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e4aAction,e4a,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv19_037d_R19_0_I1 /\ e4bAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,e4bAction,e4b,Inv19_037d_R19_0_I1,\prec,\prec
  \* (Inv19_037d_R19_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv19_037d_R19_0_I1 /\ w1aAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,w1aAction,w1a,Inv19_037d_R19_0_I1,\prec,\prec
  \* (Inv19_037d_R19_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv19_037d_R19_0_I1 /\ w1bAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,w1bAction,w1b,Inv19_037d_R19_0_I1,\prec,\prec
  \* (Inv19_037d_R19_0_I1,w2Action)
  <1>12. TypeOK /\ Inv350_b077_R20_1_I2 /\ Inv1_b58a_R20_0_I1 /\ Inv19_037d_R19_0_I1 /\ w2Action => Inv19_037d_R19_0_I1' BY DEF TypeOK,Inv350_b077_R20_1_I2,Inv1_b58a_R20_0_I1,w2Action,w2,Inv19_037d_R19_0_I1,\prec,\prec
  \* (Inv19_037d_R19_0_I1,csAction)
  <1>13. TypeOK /\ Inv19_037d_R19_0_I1 /\ csAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,csAction,cs,Inv19_037d_R19_0_I1,\prec
  \* (Inv19_037d_R19_0_I1,exitAction)
  <1>14. TypeOK /\ Inv19_037d_R19_0_I1 /\ exitAction => Inv19_037d_R19_0_I1' BY DEF TypeOK,exitAction,exit,Inv19_037d_R19_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4521_3f08_R1_1_I2
THEOREM L_27 == TypeOK /\ Inv80_b6ff_R2_0_I3 /\ Inv4521_3f08_R1_1_I2 /\ Next => Inv4521_3f08_R1_1_I2'
  <1>. USE A0
  \* (Inv4521_3f08_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ ncsAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e1aAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e1bAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e2aAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv4521_3f08_R1_1_I2,\prec,Procs
  \* (Inv4521_3f08_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e2bAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e3aAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e3bAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (Inv4521_3f08_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e4aAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ e4bAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (Inv4521_3f08_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ w1aAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (Inv4521_3f08_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv80_b6ff_R2_0_I3 /\ Inv4521_3f08_R1_1_I2 /\ w1bAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,Inv80_b6ff_R2_0_I3,w1bAction,w1b,Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (Inv4521_3f08_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ w2Action => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv4521_3f08_R1_1_I2,\prec,\prec
  \* (Inv4521_3f08_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ csAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv4521_3f08_R1_1_I2,\prec
  \* (Inv4521_3f08_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv4521_3f08_R1_1_I2 /\ exitAction => Inv4521_3f08_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv4521_3f08_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0
<1> USE DEF \prec, Procs, ProcSet
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal, Procs, ProcSet
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_MutualExclusion
    <1>2. Init => Inv4690_2f61_R0_0_I2 BY DEF Init, Inv4690_2f61_R0_0_I2, IndGlobal
    <1>3. Init => Inv4520_48f3_R1_0_I2 BY DEF Init, Inv4520_48f3_R1_0_I2, IndGlobal
    <1>4. Init => Inv10_8778_R2_0_I3 BY DEF Init, Inv10_8778_R2_0_I3, IndGlobal
    <1>5. Init => Inv5742_3d78_R2_0_I3 BY DEF Init, Inv5742_3d78_R2_0_I3, IndGlobal
    <1>6. Init => Inv11_3838_R8_0_I2 BY DEF Init, Inv11_3838_R8_0_I2, IndGlobal
    <1>7. Init => Inv61_df69_R8_0_I2 BY DEF Init, Inv61_df69_R8_0_I2, IndGlobal
    <1>8. Init => Inv1922_5e75_R2_0_I3 BY DEF Init, Inv1922_5e75_R2_0_I3, IndGlobal
    <1>9. Init => Inv4227_eecc_R10_0_I3 BY DEF Init, Inv4227_eecc_R10_0_I3, IndGlobal
    <1>10. Init => Inv2740_e784_R16_0_I3 BY DEF Init, Inv2740_e784_R16_0_I3, IndGlobal
    <1>11. Init => Inv0_b3ba_R18_0_I0 BY DEF Init, Inv0_b3ba_R18_0_I0, IndGlobal
    <1>12. Init => Inv1_b58a_R20_0_I1 BY DEF Init, Inv1_b58a_R20_0_I1, IndGlobal
    <1>13. Init => Inv350_b077_R20_1_I2 BY DEF Init, Inv350_b077_R20_1_I2, IndGlobal
    <1>14. Init => Inv40_180c_R24_0_I1 BY DEF Init, Inv40_180c_R24_0_I1, IndGlobal
    <1>15. Init => Inv6093_1c74_R18_1_I2 BY DEF Init, Inv6093_1c74_R18_1_I2, IndGlobal
    <1>16. Init => Inv103_c9b1_R21_1_I1 BY DEF Init, Inv103_c9b1_R21_1_I1, IndGlobal
    <1>17. Init => Inv80_b6ff_R2_0_I3 BY DEF Init, Inv80_b6ff_R2_0_I3, IndGlobal
    <1>18. Init => Inv140_f68c_R9_0_I1 BY DEF Init, Inv140_f68c_R9_0_I1, IndGlobal
    <1>19. Init => Inv1028_6ea5_R8_0_I2 BY DEF Init, Inv1028_6ea5_R8_0_I2, IndGlobal
    <1>20. Init => Inv24959_7f87_R1_1_I2 BY DEF Init, Inv24959_7f87_R1_1_I2, IndGlobal
    <1>21. Init => Inv5819_32cd_R1_1_I2 BY DEF Init, Inv5819_32cd_R1_1_I2, IndGlobal
    <1>22. Init => Inv4576_59b1_R1_1_I2 BY DEF Init, Inv4576_59b1_R1_1_I2, IndGlobal
    <1>23. Init => Inv4606_2f6b_R5_0_I2 BY DEF Init, Inv4606_2f6b_R5_0_I2, IndGlobal
    <1>24. Init => Inv32498_2818_R11_0_I2 BY DEF Init, Inv32498_2818_R11_0_I2, IndGlobal
    <1>25. Init => Inv3293_1a1e_R17_0_I3 BY DEF Init, Inv3293_1a1e_R17_0_I3, IndGlobal
    <1>26. Init => Inv19_037d_R19_0_I1 BY DEF Init, Inv19_037d_R19_0_I1, IndGlobal
    <1>27. Init => Inv4521_3f08_R1_1_I2 BY DEF Init, Inv4521_3f08_R1_1_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27 DEF Next, IndGlobal






\* \* Proof Graph Stats
\* \* ==================
\* \* seed: 7
\* \* num proof graph nodes: 20
\* \* num proof obligations: 280
\* Safety == H_MutualExclusion
\* Inv8417_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARI] \in {"w1","w2"}) \/ (~(pc[VARJ] = "cs")))
\* Inv4429_R1_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI})))
\* Inv4081_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "w2")))
\* Inv4491_R1_1_I2 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "cs"))
\* Inv4472_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "w2") \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))
\* Inv61_R2_0_I3 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] \in {"e4","w1","w2"}))
\* Inv6208_R3_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "w1")) \/ (~(pc[VARJ] = "cs"))
\* Inv2373_R5_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>)))
\* Inv1739_R7_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARJ] = "e4")) \/ (~(pc[VARI] = "cs"))
\* Inv5016_R8_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] \in {"w1","w2"})) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))
\* Inv31710_R9_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e3")) \/ (~(pc[VARJ] = "cs"))
\* Inv3258_R10_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] = "e3"))
\* Inv2883_R11_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ ((max[VARJ] >= num[VARI]) \/ (~(pc[VARI] = "cs")) \/ (~(pc[VARJ] = "e2")))
\* Inv3811_R12_1_I2 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3"))) \/ (~(pc[VARI] = "w2"))
\* Inv4045_R14_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[nxt[VARJ]]) \/ ((max[nxt[VARJ]] >= num[VARJ]) \/ ((pc[VARI] = "e3")) \/ (~((pc[nxt[VARJ]] = "e2"))) \/ ((pc[VARJ] = "ncs")) \/ (~(pc[VARJ] = "w2")))
\* Inv36_R14_1_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e3"))
\* Inv11_R15_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e2"))
\* Inv1_R0_0_I0 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))
\* Inv2073_R1_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"})) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}))

\* IndGlobal == 
\*   /\ TypeOK
\*   /\ Safety
\*   /\ Inv8417_R0_0_I2
\*   /\ Inv4429_R1_0_I2
\*   /\ Inv4472_R2_0_I3
\*   /\ Inv2373_R5_0_I2
\*   /\ Inv5016_R8_0_I3
\*   /\ Inv3258_R10_0_I3
\*   /\ Inv1_R0_0_I0
\*   /\ Inv2073_R1_0_I4
\*   /\ Inv4045_R14_0_I4
\*   /\ Inv11_R15_0_I1
\*   /\ Inv3811_R12_1_I2
\*   /\ Inv36_R14_1_I1
\*   /\ Inv61_R2_0_I3
\*   /\ Inv4081_R1_1_I2
\*   /\ Inv6208_R3_0_I2
\*   /\ Inv1739_R7_0_I2
\*   /\ Inv31710_R9_0_I2
\*   /\ Inv2883_R11_0_I3
\*   /\ Inv4491_R1_1_I2


\* \* mean in-degree: 1.7
\* \* median in-degree: 2
\* \* max in-degree: 3
\* \* min in-degree: 0
\* \* mean variable slice size: 0

\* ASSUME A0 == N \in Nat /\ Procs \subseteq Nat /\ IsFiniteSet(Procs)

\* \*** TypeOK
\* THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
\*   <1>. USE A0
\*   \* (TypeOK,ncsAction)
\*   <1>1. TypeOK /\ TypeOK /\ ncsAction => TypeOK'
\*        BY DEF TypeOK,ncsAction,ncs,TypeOK
\*   \* (TypeOK,e1aAction)
\*   <1>2. TypeOK /\ TypeOK /\ e1aAction => TypeOK'
\*        BY DEF TypeOK,e1aAction,e1a,TypeOK
\*   \* (TypeOK,e1bAction)
\*   <1>3. TypeOK /\ TypeOK /\ e1bAction => TypeOK'
\*        BY DEF TypeOK,e1bAction,e1b,TypeOK
\*   \* (TypeOK,e2aAction)
\*   <1>4. TypeOK /\ TypeOK /\ e2aAction => TypeOK'
\*        BY DEF TypeOK,e2aAction,e2a,TypeOK
\*   \* (TypeOK,e2bAction)
\*   <1>5. TypeOK /\ TypeOK /\ e2bAction => TypeOK'
\*        BY DEF TypeOK,e2bAction,e2b,TypeOK
\*   \* (TypeOK,e3aAction)
\*   <1>6. TypeOK /\ TypeOK /\ e3aAction => TypeOK'
\*        BY DEF TypeOK,e3aAction,e3a,TypeOK
\*   \* (TypeOK,e3bAction)
\*   <1>7. TypeOK /\ TypeOK /\ e3bAction => TypeOK'
\*        BY DEF TypeOK,e3bAction,e3b,TypeOK,\prec
\*   \* (TypeOK,e4aAction)
\*   <1>8. TypeOK /\ TypeOK /\ e4aAction => TypeOK'
\*        BY DEF TypeOK,e4aAction,e4a,TypeOK
\*   \* (TypeOK,e4bAction)
\*   <1>9. TypeOK /\ TypeOK /\ e4bAction => TypeOK'
\*        BY DEF TypeOK,e4bAction,e4b,TypeOK,\prec
\*   \* (TypeOK,w1aAction)
\*   <1>10. TypeOK /\ TypeOK /\ w1aAction => TypeOK'
\*        BY DEF TypeOK,w1aAction,w1a,TypeOK
\*   \* (TypeOK,w1bAction)
\*   <1>11. TypeOK /\ TypeOK /\ w1bAction => TypeOK'
\*        BY DEF TypeOK,w1bAction,w1b,TypeOK
\*   \* (TypeOK,w2Action)
\*   <1>12. TypeOK /\ TypeOK /\ w2Action => TypeOK'
\*        BY DEF TypeOK,w2Action,w2,TypeOK,\prec
\*   \* (TypeOK,csAction)
\*   <1>13. TypeOK /\ TypeOK /\ csAction => TypeOK'
\*        BY DEF TypeOK,csAction,cs,TypeOK
\*   \* (TypeOK,exitAction)
\*   <1>14. TypeOK /\ TypeOK /\ exitAction => TypeOK'
\*        BY DEF TypeOK,exitAction,exit,TypeOK
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \* (ROOT SAFETY PROP)
\* \*** Safety
\* THEOREM L_1 == TypeOK /\ Inv8417_R0_0_I2 /\ Safety /\ Next => Safety'
\*   <1>. USE A0
\*   \* (Safety,ncsAction)
\*   <1>1. TypeOK /\ Safety /\ ncsAction => Safety'
\*        BY DEF TypeOK,ncsAction,ncs,Safety,H_MutualExclusion
\*   \* (Safety,e1aAction)
\*   <1>2. TypeOK /\ Safety /\ e1aAction => Safety'
\*        BY DEF TypeOK,e1aAction,e1a,Safety,H_MutualExclusion
\*   \* (Safety,e1bAction)
\*   <1>3. TypeOK /\ Safety /\ e1bAction => Safety'
\*        BY DEF TypeOK,e1bAction,e1b,Safety,H_MutualExclusion
\*   \* (Safety,e2aAction)
\*   <1>4. TypeOK /\ Safety /\ e2aAction => Safety'
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Safety,
\*                         TRUE,
\*                         NEW self \in Procs,
\*                         pc[self] = "e2",
\*                         unchecked[self] # {},
\*                         NEW i \in unchecked[self],
\*                         /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
\*                         /\ IF num[i] > max[self]
\*                             THEN /\ max' = [max EXCEPT ![self] = num[i]]
\*                             ELSE /\ max' = max,
\*                         pc' = [pc EXCEPT ![self] = "e2"],
\*                         UNCHANGED << num, flag, nxt >>
\*                  PROVE  Safety'
\*       BY DEF e2a, e2aAction
\*     <2> QED
\*       BY DEF TypeOK,e2aAction,e2a,Safety,H_MutualExclusion
       
\*   \* (Safety,e2bAction)
\*   <1>5. TypeOK /\ Safety /\ e2bAction => Safety'
\*        BY DEF TypeOK,e2bAction,e2b,Safety,H_MutualExclusion
\*   \* (Safety,e3aAction)
\*   <1>6. TypeOK /\ Safety /\ e3aAction => Safety'
\*        BY DEF TypeOK,e3aAction,e3a,Safety,H_MutualExclusion
\*   \* (Safety,e3bAction)
\*   <1>7. TypeOK /\ Safety /\ e3bAction => Safety'
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Safety,
\*                         TRUE,
\*                         NEW self \in Procs,
\*                         pc[self] = "e3",
\*                         NEW i \in {j \in Nat : j > max[self]},
\*                         num' = [num EXCEPT ![self] = i],
\*                         pc' = [pc EXCEPT ![self] = "e4"],
\*                         UNCHANGED << flag, unchecked, max, nxt >>
\*                  PROVE  Safety'
\*       BY DEF e3b, e3bAction
\*     <2> QED
\*       BY DEF TypeOK,e3bAction,e3b,Safety,\prec,H_MutualExclusion
       
\*   \* (Safety,e4aAction)
\*   <1>8. TypeOK /\ Safety /\ e4aAction => Safety'
\*        BY DEF TypeOK,e4aAction,e4a,Safety,H_MutualExclusion
\*   \* (Safety,e4bAction)
\*   <1>9. TypeOK /\ Safety /\ e4bAction => Safety'
\*        BY DEF TypeOK,e4bAction,e4b,Safety,\prec,H_MutualExclusion
\*   \* (Safety,w1aAction)
\*   <1>10. TypeOK /\ Safety /\ w1aAction => Safety'
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Safety,
\*                         TRUE,
\*                         NEW self \in Procs,
\*                         pc[self] = "w1",
\*                         unchecked[self] # {},
\*                         NEW i \in unchecked[self],
\*                         nxt' = [nxt EXCEPT ![self] = i],
\*                         ~ flag[nxt'[self]],
\*                         pc' = [pc EXCEPT ![self] = "w2"],
\*                         UNCHANGED << num, flag, unchecked, max >>
\*                  PROVE  Safety'
\*       BY DEF w1a, w1aAction
\*     <2> QED
\*       BY DEF TypeOK,w1aAction,w1a,Safety,H_MutualExclusion
       
\*   \* (Safety,w1bAction)
\*   <1>11. TypeOK /\ Inv8417_R0_0_I2 /\ Safety /\ w1bAction => Safety'
\*        BY DEF TypeOK,Inv8417_R0_0_I2,w1bAction,w1b,Safety,H_MutualExclusion
\*   \* (Safety,w2Action)
\*   <1>12. TypeOK /\ Safety /\ w2Action => Safety'
\*        BY DEF TypeOK,w2Action,w2,Safety,\prec,H_MutualExclusion
\*   \* (Safety,csAction)
\*   <1>13. TypeOK /\ Safety /\ csAction => Safety'
\*        BY DEF TypeOK,csAction,cs,Safety,H_MutualExclusion
\*   \* (Safety,exitAction)
\*   <1>14. TypeOK /\ Safety /\ exitAction => Safety'
\*        BY DEF TypeOK,exitAction,exit,Safety,H_MutualExclusion
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv8417_R0_0_I2
\* THEOREM L_2 == TypeOK /\ Inv4429_R1_0_I2 /\ Inv4081_R1_1_I2 /\ Inv4491_R1_1_I2 /\ Inv8417_R0_0_I2 /\ Next => Inv8417_R0_0_I2'
\*   <1>. USE A0
\*   \* (Inv8417_R0_0_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv8417_R0_0_I2 /\ ncsAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv8417_R0_0_I2 /\ e1aAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv8417_R0_0_I2 /\ e1bAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv8417_R0_0_I2 /\ e2aAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv8417_R0_0_I2 /\ e2bAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv8417_R0_0_I2 /\ e3aAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv8417_R0_0_I2 /\ e3bAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv8417_R0_0_I2,\prec
\*   \* (Inv8417_R0_0_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv8417_R0_0_I2 /\ e4aAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv8417_R0_0_I2 /\ e4bAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv8417_R0_0_I2,\prec
\*   \* (Inv8417_R0_0_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv8417_R0_0_I2 /\ w1aAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv4429_R1_0_I2 /\ Inv8417_R0_0_I2 /\ w1bAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,Inv4429_R1_0_I2,w1bAction,w1b,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,w2Action)
\*   <1>12. TypeOK /\ Inv4081_R1_1_I2 /\ Inv4491_R1_1_I2 /\ Inv8417_R0_0_I2 /\ w2Action => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,Inv4081_R1_1_I2,Inv4491_R1_1_I2,w2Action,w2,Inv8417_R0_0_I2,\prec
\*   \* (Inv8417_R0_0_I2,csAction)
\*   <1>13. TypeOK /\ Inv8417_R0_0_I2 /\ csAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,csAction,cs,Inv8417_R0_0_I2
\*   \* (Inv8417_R0_0_I2,exitAction)
\*   <1>14. TypeOK /\ Inv8417_R0_0_I2 /\ exitAction => Inv8417_R0_0_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv8417_R0_0_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv4429_R1_0_I2
\* THEOREM L_3 == TypeOK /\ Inv4472_R2_0_I3 /\ Inv61_R2_0_I3 /\ Inv4429_R1_0_I2 /\ Next => Inv4429_R1_0_I2'
\*   <1>. USE A0
\*   \* (Inv4429_R1_0_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv4429_R1_0_I2 /\ ncsAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv4429_R1_0_I2 /\ e1aAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv4429_R1_0_I2 /\ e1bAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv4429_R1_0_I2 /\ e2aAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv4429_R1_0_I2 /\ e2bAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv4429_R1_0_I2 /\ e3aAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv4429_R1_0_I2 /\ e3bAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv4429_R1_0_I2,\prec
\*   \* (Inv4429_R1_0_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv4429_R1_0_I2 /\ e4aAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv4429_R1_0_I2 /\ e4bAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv4429_R1_0_I2,\prec
\*   \* (Inv4429_R1_0_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv4429_R1_0_I2 /\ w1aAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv4429_R1_0_I2 /\ w1bAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,w1bAction,w1b,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,w2Action)
\*   <1>12. TypeOK /\ Inv4472_R2_0_I3 /\ Inv61_R2_0_I3 /\ Inv4429_R1_0_I2 /\ w2Action => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,Inv4472_R2_0_I3,Inv61_R2_0_I3,w2Action,w2,Inv4429_R1_0_I2,\prec
\*   \* (Inv4429_R1_0_I2,csAction)
\*   <1>13. TypeOK /\ Inv4429_R1_0_I2 /\ csAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,csAction,cs,Inv4429_R1_0_I2
\*   \* (Inv4429_R1_0_I2,exitAction)
\*   <1>14. TypeOK /\ Inv4429_R1_0_I2 /\ exitAction => Inv4429_R1_0_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv4429_R1_0_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv4472_R2_0_I3
\* THEOREM L_4 == TypeOK /\ Inv2373_R5_0_I2 /\ Inv61_R2_0_I3 /\ Inv4472_R2_0_I3 /\ Next => Inv4472_R2_0_I3'
\*   <1>. USE A0
\*   \* (Inv4472_R2_0_I3,ncsAction)
\*   <1>1. TypeOK /\ Inv4472_R2_0_I3 /\ ncsAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,ncsAction,ncs,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e1aAction)
\*   <1>2. TypeOK /\ Inv4472_R2_0_I3 /\ e1aAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e1aAction,e1a,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e1bAction)
\*   <1>3. TypeOK /\ Inv4472_R2_0_I3 /\ e1bAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e1bAction,e1b,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e2aAction)
\*   <1>4. TypeOK /\ Inv4472_R2_0_I3 /\ e2aAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e2aAction,e2a,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e2bAction)
\*   <1>5. TypeOK /\ Inv4472_R2_0_I3 /\ e2bAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e2bAction,e2b,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e3aAction)
\*   <1>6. TypeOK /\ Inv4472_R2_0_I3 /\ e3aAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e3aAction,e3a,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e3bAction)
\*   <1>7. TypeOK /\ Inv4472_R2_0_I3 /\ e3bAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e3bAction,e3b,Inv4472_R2_0_I3,\prec
\*   \* (Inv4472_R2_0_I3,e4aAction)
\*   <1>8. TypeOK /\ Inv4472_R2_0_I3 /\ e4aAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e4aAction,e4a,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,e4bAction)
\*   <1>9. TypeOK /\ Inv4472_R2_0_I3 /\ e4bAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,e4bAction,e4b,Inv4472_R2_0_I3,\prec
\*   \* (Inv4472_R2_0_I3,w1aAction)
\*   <1>10. TypeOK /\ Inv2373_R5_0_I2 /\ Inv4472_R2_0_I3 /\ w1aAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,Inv2373_R5_0_I2,w1aAction,w1a,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,w1bAction)
\*   <1>11. TypeOK /\ Inv4472_R2_0_I3 /\ w1bAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,w1bAction,w1b,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,w2Action)
\*   <1>12. TypeOK /\ Inv61_R2_0_I3 /\ Inv4472_R2_0_I3 /\ w2Action => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,Inv61_R2_0_I3,w2Action,w2,Inv4472_R2_0_I3,\prec
\*   \* (Inv4472_R2_0_I3,csAction)
\*   <1>13. TypeOK /\ Inv4472_R2_0_I3 /\ csAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,csAction,cs,Inv4472_R2_0_I3
\*   \* (Inv4472_R2_0_I3,exitAction)
\*   <1>14. TypeOK /\ Inv4472_R2_0_I3 /\ exitAction => Inv4472_R2_0_I3'
\*        BY DEF TypeOK,exitAction,exit,Inv4472_R2_0_I3
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv2373_R5_0_I2
\* THEOREM L_5 == TypeOK /\ Inv5016_R8_0_I3 /\ Inv4472_R2_0_I3 /\ Inv61_R2_0_I3 /\ Inv2373_R5_0_I2 /\ Next => Inv2373_R5_0_I2'
\*   <1>. USE A0
\*   \* (Inv2373_R5_0_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv2373_R5_0_I2 /\ ncsAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv2373_R5_0_I2 /\ e1aAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv2373_R5_0_I2 /\ e1bAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv2373_R5_0_I2 /\ e2aAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv2373_R5_0_I2 /\ e2bAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv2373_R5_0_I2 /\ e3aAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv2373_R5_0_I2 /\ e3bAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv2373_R5_0_I2,\prec
\*   \* (Inv2373_R5_0_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv2373_R5_0_I2 /\ e4aAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv5016_R8_0_I3 /\ Inv2373_R5_0_I2 /\ e4bAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,Inv5016_R8_0_I3,e4bAction,e4b,Inv2373_R5_0_I2,\prec
\*   \* (Inv2373_R5_0_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv2373_R5_0_I2 /\ w1aAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv2373_R5_0_I2 /\ w1bAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,w1bAction,w1b,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,w2Action)
\*   <1>12. TypeOK /\ Inv4472_R2_0_I3 /\ Inv61_R2_0_I3 /\ Inv2373_R5_0_I2 /\ w2Action => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,Inv4472_R2_0_I3,Inv61_R2_0_I3,w2Action,w2,Inv2373_R5_0_I2,\prec
\*   \* (Inv2373_R5_0_I2,csAction)
\*   <1>13. TypeOK /\ Inv2373_R5_0_I2 /\ csAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,csAction,cs,Inv2373_R5_0_I2
\*   \* (Inv2373_R5_0_I2,exitAction)
\*   <1>14. TypeOK /\ Inv2373_R5_0_I2 /\ exitAction => Inv2373_R5_0_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv2373_R5_0_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv5016_R8_0_I3
\* THEOREM L_6 == TypeOK /\ Inv3258_R10_0_I3 /\ Inv61_R2_0_I3 /\ Inv5016_R8_0_I3 /\ Next => Inv5016_R8_0_I3'
\*   <1>. USE A0
\*   \* (Inv5016_R8_0_I3,ncsAction)
\*   <1>1. TypeOK /\ Inv5016_R8_0_I3 /\ ncsAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,ncsAction,ncs,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e1aAction)
\*   <1>2. TypeOK /\ Inv5016_R8_0_I3 /\ e1aAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e1aAction,e1a,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e1bAction)
\*   <1>3. TypeOK /\ Inv5016_R8_0_I3 /\ e1bAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e1bAction,e1b,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e2aAction)
\*   <1>4. TypeOK /\ Inv5016_R8_0_I3 /\ e2aAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e2aAction,e2a,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e2bAction)
\*   <1>5. TypeOK /\ Inv5016_R8_0_I3 /\ e2bAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e2bAction,e2b,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e3aAction)
\*   <1>6. TypeOK /\ Inv5016_R8_0_I3 /\ e3aAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e3aAction,e3a,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e3bAction)
\*   <1>7. TypeOK /\ Inv3258_R10_0_I3 /\ Inv5016_R8_0_I3 /\ e3bAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,Inv3258_R10_0_I3,e3bAction,e3b,Inv5016_R8_0_I3,\prec
\*   \* (Inv5016_R8_0_I3,e4aAction)
\*   <1>8. TypeOK /\ Inv5016_R8_0_I3 /\ e4aAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e4aAction,e4a,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,e4bAction)
\*   <1>9. TypeOK /\ Inv5016_R8_0_I3 /\ e4bAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,e4bAction,e4b,Inv5016_R8_0_I3,\prec
\*   \* (Inv5016_R8_0_I3,w1aAction)
\*   <1>10. TypeOK /\ Inv5016_R8_0_I3 /\ w1aAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,w1aAction,w1a,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,w1bAction)
\*   <1>11. TypeOK /\ Inv5016_R8_0_I3 /\ w1bAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,w1bAction,w1b,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,w2Action)
\*   <1>12. TypeOK /\ Inv61_R2_0_I3 /\ Inv5016_R8_0_I3 /\ w2Action => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,Inv61_R2_0_I3,w2Action,w2,Inv5016_R8_0_I3,\prec
\*   \* (Inv5016_R8_0_I3,csAction)
\*   <1>13. TypeOK /\ Inv5016_R8_0_I3 /\ csAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,csAction,cs,Inv5016_R8_0_I3
\*   \* (Inv5016_R8_0_I3,exitAction)
\*   <1>14. TypeOK /\ Inv5016_R8_0_I3 /\ exitAction => Inv5016_R8_0_I3'
\*        BY DEF TypeOK,exitAction,exit,Inv5016_R8_0_I3
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv3258_R10_0_I3
\* THEOREM L_7 == TypeOK /\ Inv1_R0_0_I0 /\ Inv3811_R12_1_I2 /\ Inv3811_R12_1_I2 /\ Inv3258_R10_0_I3 /\ Next => Inv3258_R10_0_I3'
\*   <1>. USE A0
\*   \* (Inv3258_R10_0_I3,ncsAction)
\*   <1>1. TypeOK /\ Inv3258_R10_0_I3 /\ ncsAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,ncsAction,ncs,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e1aAction)
\*   <1>2. TypeOK /\ Inv3258_R10_0_I3 /\ e1aAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e1aAction,e1a,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e1bAction)
\*   <1>3. TypeOK /\ Inv3258_R10_0_I3 /\ e1bAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e1bAction,e1b,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e2aAction)
\*   <1>4. TypeOK /\ Inv3258_R10_0_I3 /\ e2aAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e2aAction,e2a,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e2bAction)
\*   <1>5. TypeOK /\ Inv1_R0_0_I0 /\ Inv3258_R10_0_I3 /\ e2bAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,Inv1_R0_0_I0,e2bAction,e2b,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e3aAction)
\*   <1>6. TypeOK /\ Inv3258_R10_0_I3 /\ e3aAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e3aAction,e3a,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e3bAction)
\*   <1>7. TypeOK /\ Inv3258_R10_0_I3 /\ e3bAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e3bAction,e3b,Inv3258_R10_0_I3,\prec
\*   \* (Inv3258_R10_0_I3,e4aAction)
\*   <1>8. TypeOK /\ Inv3258_R10_0_I3 /\ e4aAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e4aAction,e4a,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,e4bAction)
\*   <1>9. TypeOK /\ Inv3258_R10_0_I3 /\ e4bAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,e4bAction,e4b,Inv3258_R10_0_I3,\prec
\*   \* (Inv3258_R10_0_I3,w1aAction)
\*   <1>10. TypeOK /\ Inv3258_R10_0_I3 /\ w1aAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,w1aAction,w1a,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,w1bAction)
\*   <1>11. TypeOK /\ Inv3258_R10_0_I3 /\ w1bAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,w1bAction,w1b,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,w2Action)
\*   <1>12. TypeOK /\ Inv3811_R12_1_I2 /\ Inv3811_R12_1_I2 /\ Inv3258_R10_0_I3 /\ w2Action => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,Inv3811_R12_1_I2,Inv3811_R12_1_I2,w2Action,w2,Inv3258_R10_0_I3,\prec
\*   \* (Inv3258_R10_0_I3,csAction)
\*   <1>13. TypeOK /\ Inv3258_R10_0_I3 /\ csAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,csAction,cs,Inv3258_R10_0_I3
\*   \* (Inv3258_R10_0_I3,exitAction)
\*   <1>14. TypeOK /\ Inv3258_R10_0_I3 /\ exitAction => Inv3258_R10_0_I3'
\*        BY DEF TypeOK,exitAction,exit,Inv3258_R10_0_I3
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv1_R0_0_I0
\* THEOREM L_8 == TypeOK /\ Inv2073_R1_0_I4 /\ Inv4045_R14_0_I4 /\ Inv1_R0_0_I0 /\ Next => Inv1_R0_0_I0'
\*   <1>. USE A0
\*   \* (Inv1_R0_0_I0,ncsAction)
\*   <1>1. TypeOK /\ Inv1_R0_0_I0 /\ ncsAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,ncsAction,ncs,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e1aAction)
\*   <1>2. TypeOK /\ Inv1_R0_0_I0 /\ e1aAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e1aAction,e1a,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e1bAction)
\*   <1>3. TypeOK /\ Inv1_R0_0_I0 /\ e1bAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e1bAction,e1b,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e2aAction)
\*   <1>4. TypeOK /\ Inv2073_R1_0_I4 /\ Inv1_R0_0_I0 /\ e2aAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,Inv2073_R1_0_I4,e2aAction,e2a,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e2bAction)
\*   <1>5. TypeOK /\ Inv1_R0_0_I0 /\ e2bAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e2bAction,e2b,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e3aAction)
\*   <1>6. TypeOK /\ Inv1_R0_0_I0 /\ e3aAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e3aAction,e3a,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e3bAction)
\*   <1>7. TypeOK /\ Inv1_R0_0_I0 /\ e3bAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e3bAction,e3b,Inv1_R0_0_I0,\prec
\*   \* (Inv1_R0_0_I0,e4aAction)
\*   <1>8. TypeOK /\ Inv1_R0_0_I0 /\ e4aAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e4aAction,e4a,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,e4bAction)
\*   <1>9. TypeOK /\ Inv1_R0_0_I0 /\ e4bAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,e4bAction,e4b,Inv1_R0_0_I0,\prec
\*   \* (Inv1_R0_0_I0,w1aAction)
\*   <1>10. TypeOK /\ Inv1_R0_0_I0 /\ w1aAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,w1aAction,w1a,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,w1bAction)
\*   <1>11. TypeOK /\ Inv1_R0_0_I0 /\ w1bAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,w1bAction,w1b,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,w2Action)
\*   <1>12. TypeOK /\ Inv4045_R14_0_I4 /\ Inv1_R0_0_I0 /\ w2Action => Inv1_R0_0_I0'
\*        BY DEF TypeOK,Inv4045_R14_0_I4,w2Action,w2,Inv1_R0_0_I0,\prec
\*   \* (Inv1_R0_0_I0,csAction)
\*   <1>13. TypeOK /\ Inv1_R0_0_I0 /\ csAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,csAction,cs,Inv1_R0_0_I0
\*   \* (Inv1_R0_0_I0,exitAction)
\*   <1>14. TypeOK /\ Inv1_R0_0_I0 /\ exitAction => Inv1_R0_0_I0'
\*        BY DEF TypeOK,exitAction,exit,Inv1_R0_0_I0
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv2073_R1_0_I4
\* THEOREM L_9 == TypeOK /\ Inv4045_R14_0_I4 /\ Inv2073_R1_0_I4 /\ Next => Inv2073_R1_0_I4'
\*   <1>. USE A0
\*   \* (Inv2073_R1_0_I4,ncsAction)
\*   <1>1. TypeOK /\ Inv2073_R1_0_I4 /\ ncsAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,ncsAction,ncs,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e1aAction)
\*   <1>2. TypeOK /\ Inv2073_R1_0_I4 /\ e1aAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e1aAction,e1a,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e1bAction)
\*   <1>3. TypeOK /\ Inv2073_R1_0_I4 /\ e1bAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e1bAction,e1b,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e2aAction)
\*   <1>4. TypeOK /\ Inv2073_R1_0_I4 /\ e2aAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e2aAction,e2a,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e2bAction)
\*   <1>5. TypeOK /\ Inv2073_R1_0_I4 /\ e2bAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e2bAction,e2b,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e3aAction)
\*   <1>6. TypeOK /\ Inv2073_R1_0_I4 /\ e3aAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e3aAction,e3a,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e3bAction)
\*   <1>7. TypeOK /\ Inv2073_R1_0_I4 /\ e3bAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e3bAction,e3b,Inv2073_R1_0_I4,\prec
\*   \* (Inv2073_R1_0_I4,e4aAction)
\*   <1>8. TypeOK /\ Inv2073_R1_0_I4 /\ e4aAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e4aAction,e4a,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,e4bAction)
\*   <1>9. TypeOK /\ Inv2073_R1_0_I4 /\ e4bAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,e4bAction,e4b,Inv2073_R1_0_I4,\prec
\*   \* (Inv2073_R1_0_I4,w1aAction)
\*   <1>10. TypeOK /\ Inv2073_R1_0_I4 /\ w1aAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,w1aAction,w1a,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,w1bAction)
\*   <1>11. TypeOK /\ Inv2073_R1_0_I4 /\ w1bAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,w1bAction,w1b,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,w2Action)
\*   <1>12. TypeOK /\ Inv4045_R14_0_I4 /\ Inv2073_R1_0_I4 /\ w2Action => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,Inv4045_R14_0_I4,w2Action,w2,Inv2073_R1_0_I4,\prec
\*   \* (Inv2073_R1_0_I4,csAction)
\*   <1>13. TypeOK /\ Inv2073_R1_0_I4 /\ csAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,csAction,cs,Inv2073_R1_0_I4
\*   \* (Inv2073_R1_0_I4,exitAction)
\*   <1>14. TypeOK /\ Inv2073_R1_0_I4 /\ exitAction => Inv2073_R1_0_I4'
\*        BY DEF TypeOK,exitAction,exit,Inv2073_R1_0_I4
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv4045_R14_0_I4
\* THEOREM L_10 == TypeOK /\ Inv11_R15_0_I1 /\ Inv4045_R14_0_I4 /\ Next => Inv4045_R14_0_I4'
\*   <1>. USE A0
\*   \* (Inv4045_R14_0_I4,ncsAction)
\*   <1>1. TypeOK /\ Inv4045_R14_0_I4 /\ ncsAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,ncsAction,ncs,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,e1aAction)
\*   <1>2. TypeOK /\ Inv4045_R14_0_I4 /\ e1aAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e1aAction,e1a,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,e1bAction)
\*   <1>3. TypeOK /\ Inv4045_R14_0_I4 /\ e1bAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e1bAction,e1b,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,e2aAction)
\*   <1>4. TypeOK /\ Inv4045_R14_0_I4 /\ e2aAction => Inv4045_R14_0_I4'
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv4045_R14_0_I4,
\*                         TRUE,
\*                         NEW self \in Procs,
\*                         pc[self] = "e2",
\*                         unchecked[self] # {},
\*                         NEW i \in unchecked[self],
\*                         /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
\*                         /\ IF num[i] > max[self]
\*                             THEN /\ max' = [max EXCEPT ![self] = num[i]]
\*                             ELSE /\ max' = max,
\*                         pc' = [pc EXCEPT ![self] = "e2"],
\*                         UNCHANGED << num, flag, nxt >>,
\*                         NEW VARI \in Procs',
\*                         NEW VARJ \in Procs'
\*                  PROVE  ((VARJ \in unchecked[nxt[VARJ]]) \/ ((max[nxt[VARJ]] >= num[VARJ]) \/ ((pc[VARI] = "e3")) \/ (~((pc[nxt[VARJ]] = "e2"))) \/ ((pc[VARJ] = "ncs")) \/ (~(pc[VARJ] = "w2"))))'
\*       BY DEF Inv4045_R14_0_I4, e2a, e2aAction
\*     <2> QED
\*       BY FS_Singleton,FS_Subset,FS_Difference DEF TypeOK,e2aAction,e2a,Inv4045_R14_0_I4,Inv11_R15_0_I1, Procs
       
       
\*   \* (Inv4045_R14_0_I4,e2bAction)
\*   <1>5. TypeOK /\ Inv4045_R14_0_I4 /\ e2bAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e2bAction,e2b,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,e3aAction)
\*   <1>6. TypeOK /\ Inv4045_R14_0_I4 /\ e3aAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e3aAction,e3a,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,e3bAction)
\*   <1>7. TypeOK /\ Inv4045_R14_0_I4 /\ e3bAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e3bAction,e3b,Inv4045_R14_0_I4,\prec
\*   \* (Inv4045_R14_0_I4,e4aAction)
\*   <1>8. TypeOK /\ Inv4045_R14_0_I4 /\ e4aAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e4aAction,e4a,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,e4bAction)
\*   <1>9. TypeOK /\ Inv4045_R14_0_I4 /\ e4bAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,e4bAction,e4b,Inv4045_R14_0_I4,\prec
\*   \* (Inv4045_R14_0_I4,w1aAction)
\*   <1>10. TypeOK /\ Inv11_R15_0_I1 /\ Inv4045_R14_0_I4 /\ w1aAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,Inv11_R15_0_I1,w1aAction,w1a,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,w1bAction)
\*   <1>11. TypeOK /\ Inv4045_R14_0_I4 /\ w1bAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,w1bAction,w1b,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,w2Action)
\*   <1>12. TypeOK /\ Inv4045_R14_0_I4 /\ w2Action => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,w2Action,w2,Inv4045_R14_0_I4,\prec
\*   \* (Inv4045_R14_0_I4,csAction)
\*   <1>13. TypeOK /\ Inv4045_R14_0_I4 /\ csAction => Inv4045_R14_0_I4'
\*        BY DEF TypeOK,csAction,cs,Inv4045_R14_0_I4
\*   \* (Inv4045_R14_0_I4,exitAction)
\*   <1>14. TypeOK /\ Inv4045_R14_0_I4 /\ exitAction => Inv4045_R14_0_I4'
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv4045_R14_0_I4,
\*                         TRUE,
\*                         NEW self \in Procs,
\*                         pc[self] = "exit",
\*                         UNCHANGED << flag, unchecked, max, nxt >>,
\*                         NEW VARI \in Procs',
\*                         NEW VARJ \in Procs',
\*                         \/ /\ \E k \in Nat:
\*                                 num' = [num EXCEPT ![self] = k]
\*                            /\ pc' = [pc EXCEPT ![self] = "exit"]
\*                         \/ /\ num' = [num EXCEPT ![self] = 0]
\*                            /\ pc' = [pc EXCEPT ![self] = "ncs"]
\*                  PROVE  ((VARJ \in unchecked[nxt[VARJ]]) \/ ((max[nxt[VARJ]] >= num[VARJ]) \/ ((pc[VARI] = "e3")) \/ (~((pc[nxt[VARJ]] = "e2"))) \/ ((pc[VARJ] = "ncs")) \/ (~(pc[VARJ] = "w2"))))'
\*       BY DEF Inv4045_R14_0_I4, exit, exitAction
\*     <2>1. CASE /\ \E k \in Nat:
\*                     num' = [num EXCEPT ![self] = k]
\*                /\ pc' = [pc EXCEPT ![self] = "exit"]
\*       BY <2>1 DEF TypeOK,exitAction,exit,Inv4045_R14_0_I4
\*     <2>2. CASE /\ num' = [num EXCEPT ![self] = 0]
\*                /\ pc' = [pc EXCEPT ![self] = "ncs"]
\*       BY <2>2 DEF TypeOK,exitAction,exit,Inv4045_R14_0_I4
\*     <2>3. QED
\*       BY <2>1, <2>2
       
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv11_R15_0_I1
\* THEOREM L_11 == TypeOK /\ Inv11_R15_0_I1 /\ Next => Inv11_R15_0_I1'
\*   <1>. USE A0
\*   \* (Inv11_R15_0_I1,ncsAction)
\*   <1>1. TypeOK /\ Inv11_R15_0_I1 /\ ncsAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,ncsAction,ncs,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e1aAction)
\*   <1>2. TypeOK /\ Inv11_R15_0_I1 /\ e1aAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e1aAction,e1a,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e1bAction)
\*   <1>3. TypeOK /\ Inv11_R15_0_I1 /\ e1bAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e1bAction,e1b,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e2aAction)
\*   <1>4. TypeOK /\ Inv11_R15_0_I1 /\ e2aAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e2aAction,e2a,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e2bAction)
\*   <1>5. TypeOK /\ Inv11_R15_0_I1 /\ e2bAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e2bAction,e2b,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e3aAction)
\*   <1>6. TypeOK /\ Inv11_R15_0_I1 /\ e3aAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e3aAction,e3a,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e3bAction)
\*   <1>7. TypeOK /\ Inv11_R15_0_I1 /\ e3bAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e3bAction,e3b,Inv11_R15_0_I1,\prec
\*   \* (Inv11_R15_0_I1,e4aAction)
\*   <1>8. TypeOK /\ Inv11_R15_0_I1 /\ e4aAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e4aAction,e4a,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,e4bAction)
\*   <1>9. TypeOK /\ Inv11_R15_0_I1 /\ e4bAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,e4bAction,e4b,Inv11_R15_0_I1,\prec
\*   \* (Inv11_R15_0_I1,w1aAction)
\*   <1>10. TypeOK /\ Inv11_R15_0_I1 /\ w1aAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,w1aAction,w1a,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,w1bAction)
\*   <1>11. TypeOK /\ Inv11_R15_0_I1 /\ w1bAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,w1bAction,w1b,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,w2Action)
\*   <1>12. TypeOK /\ Inv11_R15_0_I1 /\ w2Action => Inv11_R15_0_I1'
\*        BY DEF TypeOK,w2Action,w2,Inv11_R15_0_I1,\prec
\*   \* (Inv11_R15_0_I1,csAction)
\*   <1>13. TypeOK /\ Inv11_R15_0_I1 /\ csAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,csAction,cs,Inv11_R15_0_I1
\*   \* (Inv11_R15_0_I1,exitAction)
\*   <1>14. TypeOK /\ Inv11_R15_0_I1 /\ exitAction => Inv11_R15_0_I1'
\*        BY DEF TypeOK,exitAction,exit,Inv11_R15_0_I1
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv3811_R12_1_I2
\* THEOREM L_12 == TypeOK /\ Inv4045_R14_0_I4 /\ Inv36_R14_1_I1 /\ Inv3811_R12_1_I2 /\ Next => Inv3811_R12_1_I2'
\*   <1>. USE A0
\*   \* (Inv3811_R12_1_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv3811_R12_1_I2 /\ ncsAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv3811_R12_1_I2 /\ e1aAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv3811_R12_1_I2 /\ e1bAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv3811_R12_1_I2 /\ e2aAction => Inv3811_R12_1_I2'
\*     <2> SUFFICES ASSUME TypeOK,
\*                         Inv3811_R12_1_I2,
\*                         TRUE,
\*                         NEW self \in Procs,
\*                         pc[self] = "e2",
\*                         unchecked[self] # {},
\*                         NEW i \in unchecked[self],
\*                         /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
\*                         /\ IF num[i] > max[self]
\*                             THEN /\ max' = [max EXCEPT ![self] = num[i]]
\*                             ELSE /\ max' = max,
\*                         pc' = [pc EXCEPT ![self] = "e2"],
\*                         UNCHANGED << num, flag, nxt >>,
\*                         NEW VARI \in Procs'
\*                  PROVE  ((max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3"))) \/ (~(pc[VARI] = "w2")))'
\*       BY DEF Inv3811_R12_1_I2, e2a, e2aAction
\*     <2> QED
\*       BY DEF TypeOK,e2aAction,e2a,Inv3811_R12_1_I2
       
\*   \* (Inv3811_R12_1_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv4045_R14_0_I4 /\ Inv3811_R12_1_I2 /\ e2bAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,Inv4045_R14_0_I4,e2bAction,e2b,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv3811_R12_1_I2 /\ e3aAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv3811_R12_1_I2 /\ e3bAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv3811_R12_1_I2,\prec
\*   \* (Inv3811_R12_1_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv3811_R12_1_I2 /\ e4aAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv3811_R12_1_I2 /\ e4bAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv3811_R12_1_I2,\prec
\*   \* (Inv3811_R12_1_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv36_R14_1_I1 /\ Inv3811_R12_1_I2 /\ w1aAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,Inv36_R14_1_I1,w1aAction,w1a,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv3811_R12_1_I2 /\ w1bAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,w1bAction,w1b,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,w2Action)
\*   <1>12. TypeOK /\ Inv3811_R12_1_I2 /\ w2Action => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,w2Action,w2,Inv3811_R12_1_I2,\prec
\*   \* (Inv3811_R12_1_I2,csAction)
\*   <1>13. TypeOK /\ Inv3811_R12_1_I2 /\ csAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,csAction,cs,Inv3811_R12_1_I2
\*   \* (Inv3811_R12_1_I2,exitAction)
\*   <1>14. TypeOK /\ Inv3811_R12_1_I2 /\ exitAction => Inv3811_R12_1_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv3811_R12_1_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv36_R14_1_I1
\* THEOREM L_13 == TypeOK /\ Inv11_R15_0_I1 /\ Inv36_R14_1_I1 /\ Next => Inv36_R14_1_I1'
\*   <1>. USE A0
\*   \* (Inv36_R14_1_I1,ncsAction)
\*   <1>1. TypeOK /\ Inv36_R14_1_I1 /\ ncsAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,ncsAction,ncs,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e1aAction)
\*   <1>2. TypeOK /\ Inv36_R14_1_I1 /\ e1aAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e1aAction,e1a,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e1bAction)
\*   <1>3. TypeOK /\ Inv36_R14_1_I1 /\ e1bAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e1bAction,e1b,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e2aAction)
\*   <1>4. TypeOK /\ Inv36_R14_1_I1 /\ e2aAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e2aAction,e2a,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e2bAction)
\*   <1>5. TypeOK /\ Inv11_R15_0_I1 /\ Inv36_R14_1_I1 /\ e2bAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,Inv11_R15_0_I1,e2bAction,e2b,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e3aAction)
\*   <1>6. TypeOK /\ Inv36_R14_1_I1 /\ e3aAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e3aAction,e3a,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e3bAction)
\*   <1>7. TypeOK /\ Inv36_R14_1_I1 /\ e3bAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e3bAction,e3b,Inv36_R14_1_I1,\prec
\*   \* (Inv36_R14_1_I1,e4aAction)
\*   <1>8. TypeOK /\ Inv36_R14_1_I1 /\ e4aAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e4aAction,e4a,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,e4bAction)
\*   <1>9. TypeOK /\ Inv36_R14_1_I1 /\ e4bAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,e4bAction,e4b,Inv36_R14_1_I1,\prec
\*   \* (Inv36_R14_1_I1,w1aAction)
\*   <1>10. TypeOK /\ Inv36_R14_1_I1 /\ w1aAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,w1aAction,w1a,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,w1bAction)
\*   <1>11. TypeOK /\ Inv36_R14_1_I1 /\ w1bAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,w1bAction,w1b,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,w2Action)
\*   <1>12. TypeOK /\ Inv36_R14_1_I1 /\ w2Action => Inv36_R14_1_I1'
\*        BY DEF TypeOK,w2Action,w2,Inv36_R14_1_I1,\prec
\*   \* (Inv36_R14_1_I1,csAction)
\*   <1>13. TypeOK /\ Inv36_R14_1_I1 /\ csAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,csAction,cs,Inv36_R14_1_I1
\*   \* (Inv36_R14_1_I1,exitAction)
\*   <1>14. TypeOK /\ Inv36_R14_1_I1 /\ exitAction => Inv36_R14_1_I1'
\*        BY DEF TypeOK,exitAction,exit,Inv36_R14_1_I1
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv61_R2_0_I3
\* THEOREM L_14 == TypeOK /\ Inv61_R2_0_I3 /\ Next => Inv61_R2_0_I3'
\*   <1>. USE A0
\*   \* (Inv61_R2_0_I3,ncsAction)
\*   <1>1. TypeOK /\ Inv61_R2_0_I3 /\ ncsAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,ncsAction,ncs,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e1aAction)
\*   <1>2. TypeOK /\ Inv61_R2_0_I3 /\ e1aAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e1aAction,e1a,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e1bAction)
\*   <1>3. TypeOK /\ Inv61_R2_0_I3 /\ e1bAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e1bAction,e1b,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e2aAction)
\*   <1>4. TypeOK /\ Inv61_R2_0_I3 /\ e2aAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e2aAction,e2a,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e2bAction)
\*   <1>5. TypeOK /\ Inv61_R2_0_I3 /\ e2bAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e2bAction,e2b,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e3aAction)
\*   <1>6. TypeOK /\ Inv61_R2_0_I3 /\ e3aAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e3aAction,e3a,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e3bAction)
\*   <1>7. TypeOK /\ Inv61_R2_0_I3 /\ e3bAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e3bAction,e3b,Inv61_R2_0_I3,\prec
\*   \* (Inv61_R2_0_I3,e4aAction)
\*   <1>8. TypeOK /\ Inv61_R2_0_I3 /\ e4aAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e4aAction,e4a,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,e4bAction)
\*   <1>9. TypeOK /\ Inv61_R2_0_I3 /\ e4bAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,e4bAction,e4b,Inv61_R2_0_I3,\prec
\*   \* (Inv61_R2_0_I3,w1aAction)
\*   <1>10. TypeOK /\ Inv61_R2_0_I3 /\ w1aAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,w1aAction,w1a,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,w1bAction)
\*   <1>11. TypeOK /\ Inv61_R2_0_I3 /\ w1bAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,w1bAction,w1b,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,w2Action)
\*   <1>12. TypeOK /\ Inv61_R2_0_I3 /\ w2Action => Inv61_R2_0_I3'
\*        BY DEF TypeOK,w2Action,w2,Inv61_R2_0_I3,\prec
\*   \* (Inv61_R2_0_I3,csAction)
\*   <1>13. TypeOK /\ Inv61_R2_0_I3 /\ csAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,csAction,cs,Inv61_R2_0_I3
\*   \* (Inv61_R2_0_I3,exitAction)
\*   <1>14. TypeOK /\ Inv61_R2_0_I3 /\ exitAction => Inv61_R2_0_I3'
\*        BY DEF TypeOK,exitAction,exit,Inv61_R2_0_I3
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv4081_R1_1_I2
\* THEOREM L_15 == TypeOK /\ Inv6208_R3_0_I2 /\ Inv4472_R2_0_I3 /\ Inv4081_R1_1_I2 /\ Next => Inv4081_R1_1_I2'
\*   <1>. USE A0
\*   \* (Inv4081_R1_1_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv4081_R1_1_I2 /\ ncsAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv4081_R1_1_I2 /\ e1aAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv4081_R1_1_I2 /\ e1bAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv4081_R1_1_I2 /\ e2aAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv4081_R1_1_I2 /\ e2bAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv4081_R1_1_I2 /\ e3aAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv4081_R1_1_I2 /\ e3bAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv4081_R1_1_I2,\prec
\*   \* (Inv4081_R1_1_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv4081_R1_1_I2 /\ e4aAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv4081_R1_1_I2 /\ e4bAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv4081_R1_1_I2,\prec
\*   \* (Inv4081_R1_1_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv6208_R3_0_I2 /\ Inv4081_R1_1_I2 /\ w1aAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,Inv6208_R3_0_I2,w1aAction,w1a,Inv4081_R1_1_I2,\prec
\*   \* (Inv4081_R1_1_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv4472_R2_0_I3 /\ Inv4081_R1_1_I2 /\ w1bAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,Inv4472_R2_0_I3,w1bAction,w1b,Inv4081_R1_1_I2,\prec
\*   \* (Inv4081_R1_1_I2,w2Action)
\*   <1>12. TypeOK /\ Inv4081_R1_1_I2 /\ w2Action => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,w2Action,w2,Inv4081_R1_1_I2,\prec
\*   \* (Inv4081_R1_1_I2,csAction)
\*   <1>13. TypeOK /\ Inv4081_R1_1_I2 /\ csAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,csAction,cs,Inv4081_R1_1_I2
\*   \* (Inv4081_R1_1_I2,exitAction)
\*   <1>14. TypeOK /\ Inv4081_R1_1_I2 /\ exitAction => Inv4081_R1_1_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv4081_R1_1_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv6208_R3_0_I2
\* THEOREM L_16 == TypeOK /\ Inv1739_R7_0_I2 /\ Inv2373_R5_0_I2 /\ Inv4081_R1_1_I2 /\ Inv6208_R3_0_I2 /\ Next => Inv6208_R3_0_I2'
\*   <1>. USE A0
\*   \* (Inv6208_R3_0_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv6208_R3_0_I2 /\ ncsAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv6208_R3_0_I2 /\ e1aAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv6208_R3_0_I2 /\ e1bAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv6208_R3_0_I2 /\ e2aAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv6208_R3_0_I2 /\ e2bAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv6208_R3_0_I2 /\ e3aAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv6208_R3_0_I2 /\ e3bAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv6208_R3_0_I2,\prec
\*   \* (Inv6208_R3_0_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv6208_R3_0_I2 /\ e4aAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv1739_R7_0_I2 /\ Inv6208_R3_0_I2 /\ e4bAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,Inv1739_R7_0_I2,e4bAction,e4b,Inv6208_R3_0_I2,\prec
\*   \* (Inv6208_R3_0_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv6208_R3_0_I2 /\ w1aAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv2373_R5_0_I2 /\ Inv6208_R3_0_I2 /\ w1bAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,Inv2373_R5_0_I2,w1bAction,w1b,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,w2Action)
\*   <1>12. TypeOK /\ Inv4081_R1_1_I2 /\ Inv6208_R3_0_I2 /\ w2Action => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,Inv4081_R1_1_I2,w2Action,w2,Inv6208_R3_0_I2,\prec
\*   \* (Inv6208_R3_0_I2,csAction)
\*   <1>13. TypeOK /\ Inv6208_R3_0_I2 /\ csAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,csAction,cs,Inv6208_R3_0_I2
\*   \* (Inv6208_R3_0_I2,exitAction)
\*   <1>14. TypeOK /\ Inv6208_R3_0_I2 /\ exitAction => Inv6208_R3_0_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv6208_R3_0_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv1739_R7_0_I2
\* THEOREM L_17 == TypeOK /\ Inv31710_R9_0_I2 /\ Inv5016_R8_0_I3 /\ Inv1739_R7_0_I2 /\ Next => Inv1739_R7_0_I2'
\*   <1>. USE A0
\*   \* (Inv1739_R7_0_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv1739_R7_0_I2 /\ ncsAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv1739_R7_0_I2 /\ e1aAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv1739_R7_0_I2 /\ e1bAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv1739_R7_0_I2 /\ e2aAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv1739_R7_0_I2 /\ e2bAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv1739_R7_0_I2 /\ e3aAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv31710_R9_0_I2 /\ Inv1739_R7_0_I2 /\ e3bAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,Inv31710_R9_0_I2,e3bAction,e3b,Inv1739_R7_0_I2,\prec
\*   \* (Inv1739_R7_0_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv1739_R7_0_I2 /\ e4aAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv1739_R7_0_I2 /\ e4bAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv1739_R7_0_I2,\prec
\*   \* (Inv1739_R7_0_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv1739_R7_0_I2 /\ w1aAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv5016_R8_0_I3 /\ Inv1739_R7_0_I2 /\ w1bAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,Inv5016_R8_0_I3,w1bAction,w1b,Inv1739_R7_0_I2,\prec
\*   \* (Inv1739_R7_0_I2,w2Action)
\*   <1>12. TypeOK /\ Inv1739_R7_0_I2 /\ w2Action => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,w2Action,w2,Inv1739_R7_0_I2,\prec
\*   \* (Inv1739_R7_0_I2,csAction)
\*   <1>13. TypeOK /\ Inv1739_R7_0_I2 /\ csAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,csAction,cs,Inv1739_R7_0_I2
\*   \* (Inv1739_R7_0_I2,exitAction)
\*   <1>14. TypeOK /\ Inv1739_R7_0_I2 /\ exitAction => Inv1739_R7_0_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv1739_R7_0_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv31710_R9_0_I2
\* THEOREM L_18 == TypeOK /\ Inv2883_R11_0_I3 /\ Inv3258_R10_0_I3 /\ Inv31710_R9_0_I2 /\ Next => Inv31710_R9_0_I2'
\*   <1>. USE A0
\*   \* (Inv31710_R9_0_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv31710_R9_0_I2 /\ ncsAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv31710_R9_0_I2 /\ e1aAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv31710_R9_0_I2 /\ e1bAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv31710_R9_0_I2 /\ e2aAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv2883_R11_0_I3 /\ Inv31710_R9_0_I2 /\ e2bAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,Inv2883_R11_0_I3,e2bAction,e2b,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv31710_R9_0_I2 /\ e3aAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv31710_R9_0_I2 /\ e3bAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv31710_R9_0_I2,\prec
\*   \* (Inv31710_R9_0_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv31710_R9_0_I2 /\ e4aAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv31710_R9_0_I2 /\ e4bAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv31710_R9_0_I2,\prec
\*   \* (Inv31710_R9_0_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv31710_R9_0_I2 /\ w1aAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv3258_R10_0_I3 /\ Inv31710_R9_0_I2 /\ w1bAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,Inv3258_R10_0_I3,w1bAction,w1b,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,w2Action)
\*   <1>12. TypeOK /\ Inv31710_R9_0_I2 /\ w2Action => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,w2Action,w2,Inv31710_R9_0_I2,\prec
\*   \* (Inv31710_R9_0_I2,csAction)
\*   <1>13. TypeOK /\ Inv31710_R9_0_I2 /\ csAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,csAction,cs,Inv31710_R9_0_I2
\*   \* (Inv31710_R9_0_I2,exitAction)
\*   <1>14. TypeOK /\ Inv31710_R9_0_I2 /\ exitAction => Inv31710_R9_0_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv31710_R9_0_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv2883_R11_0_I3
\* THEOREM L_19 == TypeOK /\ Inv2073_R1_0_I4 /\ Inv2883_R11_0_I3 /\ Next => Inv2883_R11_0_I3'
\*   <1>. USE A0
\*   \* (Inv2883_R11_0_I3,ncsAction)
\*   <1>1. TypeOK /\ Inv2883_R11_0_I3 /\ ncsAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,ncsAction,ncs,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e1aAction)
\*   <1>2. TypeOK /\ Inv2883_R11_0_I3 /\ e1aAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e1aAction,e1a,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e1bAction)
\*   <1>3. TypeOK /\ Inv2883_R11_0_I3 /\ e1bAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e1bAction,e1b,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e2aAction)
\*   <1>4. TypeOK /\ Inv2883_R11_0_I3 /\ e2aAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e2aAction,e2a,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e2bAction)
\*   <1>5. TypeOK /\ Inv2883_R11_0_I3 /\ e2bAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e2bAction,e2b,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e3aAction)
\*   <1>6. TypeOK /\ Inv2883_R11_0_I3 /\ e3aAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e3aAction,e3a,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e3bAction)
\*   <1>7. TypeOK /\ Inv2883_R11_0_I3 /\ e3bAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e3bAction,e3b,Inv2883_R11_0_I3,\prec
\*   \* (Inv2883_R11_0_I3,e4aAction)
\*   <1>8. TypeOK /\ Inv2883_R11_0_I3 /\ e4aAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e4aAction,e4a,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,e4bAction)
\*   <1>9. TypeOK /\ Inv2883_R11_0_I3 /\ e4bAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,e4bAction,e4b,Inv2883_R11_0_I3,\prec
\*   \* (Inv2883_R11_0_I3,w1aAction)
\*   <1>10. TypeOK /\ Inv2883_R11_0_I3 /\ w1aAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,w1aAction,w1a,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,w1bAction)
\*   <1>11. TypeOK /\ Inv2073_R1_0_I4 /\ Inv2883_R11_0_I3 /\ w1bAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,Inv2073_R1_0_I4,w1bAction,w1b,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,w2Action)
\*   <1>12. TypeOK /\ Inv2883_R11_0_I3 /\ w2Action => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,w2Action,w2,Inv2883_R11_0_I3,\prec
\*   \* (Inv2883_R11_0_I3,csAction)
\*   <1>13. TypeOK /\ Inv2883_R11_0_I3 /\ csAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,csAction,cs,Inv2883_R11_0_I3
\*   \* (Inv2883_R11_0_I3,exitAction)
\*   <1>14. TypeOK /\ Inv2883_R11_0_I3 /\ exitAction => Inv2883_R11_0_I3'
\*        BY DEF TypeOK,exitAction,exit,Inv2883_R11_0_I3
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* \*** Inv4491_R1_1_I2
\* THEOREM L_20 == TypeOK /\ Inv61_R2_0_I3 /\ Inv4491_R1_1_I2 /\ Next => Inv4491_R1_1_I2'
\*   <1>. USE A0
\*   \* (Inv4491_R1_1_I2,ncsAction)
\*   <1>1. TypeOK /\ Inv4491_R1_1_I2 /\ ncsAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,ncsAction,ncs,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e1aAction)
\*   <1>2. TypeOK /\ Inv4491_R1_1_I2 /\ e1aAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e1aAction,e1a,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e1bAction)
\*   <1>3. TypeOK /\ Inv4491_R1_1_I2 /\ e1bAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e1bAction,e1b,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e2aAction)
\*   <1>4. TypeOK /\ Inv4491_R1_1_I2 /\ e2aAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e2aAction,e2a,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e2bAction)
\*   <1>5. TypeOK /\ Inv4491_R1_1_I2 /\ e2bAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e2bAction,e2b,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e3aAction)
\*   <1>6. TypeOK /\ Inv4491_R1_1_I2 /\ e3aAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e3aAction,e3a,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e3bAction)
\*   <1>7. TypeOK /\ Inv4491_R1_1_I2 /\ e3bAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e3bAction,e3b,Inv4491_R1_1_I2,\prec
\*   \* (Inv4491_R1_1_I2,e4aAction)
\*   <1>8. TypeOK /\ Inv4491_R1_1_I2 /\ e4aAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e4aAction,e4a,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,e4bAction)
\*   <1>9. TypeOK /\ Inv4491_R1_1_I2 /\ e4bAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,e4bAction,e4b,Inv4491_R1_1_I2,\prec
\*   \* (Inv4491_R1_1_I2,w1aAction)
\*   <1>10. TypeOK /\ Inv4491_R1_1_I2 /\ w1aAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,w1aAction,w1a,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,w1bAction)
\*   <1>11. TypeOK /\ Inv61_R2_0_I3 /\ Inv4491_R1_1_I2 /\ w1bAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,Inv61_R2_0_I3,w1bAction,w1b,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,w2Action)
\*   <1>12. TypeOK /\ Inv4491_R1_1_I2 /\ w2Action => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,w2Action,w2,Inv4491_R1_1_I2,\prec
\*   \* (Inv4491_R1_1_I2,csAction)
\*   <1>13. TypeOK /\ Inv4491_R1_1_I2 /\ csAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,csAction,cs,Inv4491_R1_1_I2
\*   \* (Inv4491_R1_1_I2,exitAction)
\*   <1>14. TypeOK /\ Inv4491_R1_1_I2 /\ exitAction => Inv4491_R1_1_I2'
\*        BY DEF TypeOK,exitAction,exit,Inv4491_R1_1_I2
\* <1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next




\* \* Initiation.
\* THEOREM Init => IndGlobal
\*     <1> USE A0 DEF \prec,Procs,ProcSet,H_MutualExclusion
\*     <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal, ProcSet
\*     <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, ProcSet
\*     <1>2. Init => Inv8417_R0_0_I2 BY DEF Init, Inv8417_R0_0_I2, IndGlobal
\*     <1>3. Init => Inv4429_R1_0_I2 BY DEF Init, Inv4429_R1_0_I2, IndGlobal
\*     <1>4. Init => Inv4472_R2_0_I3 BY DEF Init, Inv4472_R2_0_I3, IndGlobal
\*     <1>5. Init => Inv2373_R5_0_I2 BY DEF Init, Inv2373_R5_0_I2, IndGlobal
\*     <1>6. Init => Inv5016_R8_0_I3 BY DEF Init, Inv5016_R8_0_I3, IndGlobal
\*     <1>7. Init => Inv3258_R10_0_I3 BY DEF Init, Inv3258_R10_0_I3, IndGlobal
\*     <1>8. Init => Inv1_R0_0_I0 BY DEF Init, Inv1_R0_0_I0, IndGlobal
\*     <1>9. Init => Inv2073_R1_0_I4 BY DEF Init, Inv2073_R1_0_I4, IndGlobal
\*     <1>10. Init => Inv4045_R14_0_I4 BY DEF Init, Inv4045_R14_0_I4, IndGlobal
\*     <1>11. Init => Inv11_R15_0_I1 BY DEF Init, Inv11_R15_0_I1, IndGlobal
\*     <1>12. Init => Inv3811_R12_1_I2 BY DEF Init, Inv3811_R12_1_I2, IndGlobal
\*     <1>13. Init => Inv36_R14_1_I1 BY DEF Init, Inv36_R14_1_I1, IndGlobal
\*     <1>14. Init => Inv61_R2_0_I3 BY DEF Init, Inv61_R2_0_I3, IndGlobal
\*     <1>15. Init => Inv4081_R1_1_I2 BY DEF Init, Inv4081_R1_1_I2, IndGlobal
\*     <1>16. Init => Inv6208_R3_0_I2 BY DEF Init, Inv6208_R3_0_I2, IndGlobal
\*     <1>17. Init => Inv1739_R7_0_I2 BY DEF Init, Inv1739_R7_0_I2, IndGlobal
\*     <1>18. Init => Inv31710_R9_0_I2 BY DEF Init, Inv31710_R9_0_I2, IndGlobal
\*     <1>19. Init => Inv2883_R11_0_I3 BY DEF Init, Inv2883_R11_0_I3, IndGlobal
\*     <1>20. Init => Inv4491_R1_1_I2 BY DEF Init, Inv4491_R1_1_I2, IndGlobal
\*     <1>22. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20 DEF IndGlobal



\* THEOREM IndGlobal /\ Next => IndGlobal'
\*   BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20 DEF Next, IndGlobal
  


\* Inv21195_R4_0_I3 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARI] = "w1"))
=============================================================================
\* Modification History
\* Last modified Wed Oct 02 17:18:06 EDT 2024 by willyschultz
\* Last modified Tue Dec 18 13:48:46 PST 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
