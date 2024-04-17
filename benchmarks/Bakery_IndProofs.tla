------------------------------- MODULE Bakery_IndProofs -------------------------------
EXTENDS Bakery

\* Proof Graph Stats
\* ==================
\* seed: 7
\* num proof graph nodes: 20
\* num proof obligations: 280
\* date: 4/16/2024
Safety == H_MutualExclusion
Inv8417_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARI] \in {"w1","w2"}) \/ (~(pc[VARJ] = "cs")))
Inv4429_R1_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI})))
Inv4081_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "w2")))
Inv4491_R1_1_I2 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "cs"))
Inv4472_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "w2") \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))
Inv61_R2_0_I3 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] \in {"e4","w1","w2"}))
Inv6208_R3_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "w1")) \/ (~(pc[VARJ] = "cs"))
Inv2373_R5_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>)))
Inv1739_R7_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARJ] = "e4")) \/ (~(pc[VARI] = "cs"))
Inv5016_R8_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] \in {"w1","w2"})) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))
Inv31710_R9_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e3")) \/ (~(pc[VARJ] = "cs"))
Inv3258_R10_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] = "e3"))
Inv2883_R11_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ ((max[VARJ] >= num[VARI]) \/ (~(pc[VARI] = "cs")) \/ (~(pc[VARJ] = "e2")))
Inv3811_R12_1_I2 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3"))) \/ (~(pc[VARI] = "w2"))
Inv4045_R14_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[nxt[VARJ]]) \/ ((max[nxt[VARJ]] >= num[VARJ]) \/ ((pc[VARI] = "e3")) \/ (~((pc[nxt[VARJ]] = "e2"))) \/ ((pc[VARJ] = "ncs")) \/ (~(pc[VARJ] = "w2")))
Inv36_R14_1_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e3"))
Inv11_R15_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e2"))
Inv1_R0_0_I0 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))
Inv2073_R1_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"})) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv8417_R0_0_I2
  /\ Inv4429_R1_0_I2
  /\ Inv4472_R2_0_I3
  /\ Inv2373_R5_0_I2
  /\ Inv5016_R8_0_I3
  /\ Inv3258_R10_0_I3
  /\ Inv1_R0_0_I0
  /\ Inv2073_R1_0_I4
  /\ Inv4045_R14_0_I4
  /\ Inv11_R15_0_I1
  /\ Inv3811_R12_1_I2
  /\ Inv36_R14_1_I1
  /\ Inv61_R2_0_I3
  /\ Inv4081_R1_1_I2
  /\ Inv6208_R3_0_I2
  /\ Inv1739_R7_0_I2
  /\ Inv31710_R9_0_I2
  /\ Inv2883_R11_0_I3
  /\ Inv4491_R1_1_I2


\* mean in-degree: 1.05
\* median in-degree: 1
\* max in-degree: 3
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,ncsAction)
  <1>1. TypeOK /\ TypeOK /\ ncsAction => TypeOK'
       BY DEF TypeOK,ncsAction,ncs,TypeOK
  \* (TypeOK,e1aAction)
  <1>2. TypeOK /\ TypeOK /\ e1aAction => TypeOK'
       BY DEF TypeOK,e1aAction,e1a,TypeOK
  \* (TypeOK,e1bAction)
  <1>3. TypeOK /\ TypeOK /\ e1bAction => TypeOK'
       BY DEF TypeOK,e1bAction,e1b,TypeOK
  \* (TypeOK,e2aAction)
  <1>4. TypeOK /\ TypeOK /\ e2aAction => TypeOK'
       BY DEF TypeOK,e2aAction,e2a,TypeOK
  \* (TypeOK,e2bAction)
  <1>5. TypeOK /\ TypeOK /\ e2bAction => TypeOK'
       BY DEF TypeOK,e2bAction,e2b,TypeOK
  \* (TypeOK,e3aAction)
  <1>6. TypeOK /\ TypeOK /\ e3aAction => TypeOK'
       BY DEF TypeOK,e3aAction,e3a,TypeOK
  \* (TypeOK,e3bAction)
  <1>7. TypeOK /\ TypeOK /\ e3bAction => TypeOK'
       BY DEF TypeOK,e3bAction,e3b,TypeOK
  \* (TypeOK,e4aAction)
  <1>8. TypeOK /\ TypeOK /\ e4aAction => TypeOK'
       BY DEF TypeOK,e4aAction,e4a,TypeOK
  \* (TypeOK,e4bAction)
  <1>9. TypeOK /\ TypeOK /\ e4bAction => TypeOK'
       BY DEF TypeOK,e4bAction,e4b,TypeOK
  \* (TypeOK,w1aAction)
  <1>10. TypeOK /\ TypeOK /\ w1aAction => TypeOK'
       BY DEF TypeOK,w1aAction,w1a,TypeOK
  \* (TypeOK,w1bAction)
  <1>11. TypeOK /\ TypeOK /\ w1bAction => TypeOK'
       BY DEF TypeOK,w1bAction,w1b,TypeOK
  \* (TypeOK,w2Action)
  <1>12. TypeOK /\ TypeOK /\ w2Action => TypeOK'
       BY DEF TypeOK,w2Action,w2,TypeOK
  \* (TypeOK,csAction)
  <1>13. TypeOK /\ TypeOK /\ csAction => TypeOK'
       BY DEF TypeOK,csAction,cs,TypeOK
  \* (TypeOK,exitAction)
  <1>14. TypeOK /\ TypeOK /\ exitAction => TypeOK'
       BY DEF TypeOK,exitAction,exit,TypeOK
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv8417_R0_0_I2 /\ Safety /\ Next => Safety'
  \* (Safety,ncsAction)
  <1>1. TypeOK /\ Safety /\ ncsAction => Safety'
       BY DEF TypeOK,ncsAction,ncs,Safety,H_MutualExclusion
  \* (Safety,e1aAction)
  <1>2. TypeOK /\ Safety /\ e1aAction => Safety'
       BY DEF TypeOK,e1aAction,e1a,Safety,H_MutualExclusion
  \* (Safety,e1bAction)
  <1>3. TypeOK /\ Safety /\ e1bAction => Safety'
       BY DEF TypeOK,e1bAction,e1b,Safety,H_MutualExclusion
  \* (Safety,e2aAction)
  <1>4. TypeOK /\ Safety /\ e2aAction => Safety'
       BY DEF TypeOK,e2aAction,e2a,Safety,H_MutualExclusion
  \* (Safety,e2bAction)
  <1>5. TypeOK /\ Safety /\ e2bAction => Safety'
       BY DEF TypeOK,e2bAction,e2b,Safety,H_MutualExclusion
  \* (Safety,e3aAction)
  <1>6. TypeOK /\ Safety /\ e3aAction => Safety'
       BY DEF TypeOK,e3aAction,e3a,Safety,H_MutualExclusion
  \* (Safety,e3bAction)
  <1>7. TypeOK /\ Safety /\ e3bAction => Safety'
       BY DEF TypeOK,e3bAction,e3b,Safety,H_MutualExclusion
  \* (Safety,e4aAction)
  <1>8. TypeOK /\ Safety /\ e4aAction => Safety'
       BY DEF TypeOK,e4aAction,e4a,Safety,H_MutualExclusion
  \* (Safety,e4bAction)
  <1>9. TypeOK /\ Safety /\ e4bAction => Safety'
       BY DEF TypeOK,e4bAction,e4b,Safety,H_MutualExclusion
  \* (Safety,w1aAction)
  <1>10. TypeOK /\ Safety /\ w1aAction => Safety'
       BY DEF TypeOK,w1aAction,w1a,Safety,H_MutualExclusion
  \* (Safety,w1bAction)
  <1>11. TypeOK /\ Inv8417_R0_0_I2 /\ Safety /\ w1bAction => Safety'
       BY DEF TypeOK,Inv8417_R0_0_I2,w1bAction,w1b,Safety,H_MutualExclusion
  \* (Safety,w2Action)
  <1>12. TypeOK /\ Safety /\ w2Action => Safety'
       BY DEF TypeOK,w2Action,w2,Safety,H_MutualExclusion
  \* (Safety,csAction)
  <1>13. TypeOK /\ Safety /\ csAction => Safety'
       BY DEF TypeOK,csAction,cs,Safety,H_MutualExclusion
  \* (Safety,exitAction)
  <1>14. TypeOK /\ Safety /\ exitAction => Safety'
       BY DEF TypeOK,exitAction,exit,Safety,H_MutualExclusion
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv8417_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv4429_R1_0_I2 /\ Inv4081_R1_1_I2 /\ Inv4491_R1_1_I2 /\ Inv8417_R0_0_I2 /\ Next => Inv8417_R0_0_I2'
  \* (Inv8417_R0_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv8417_R0_0_I2 /\ ncsAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv8417_R0_0_I2 /\ e1aAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv8417_R0_0_I2 /\ e1bAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv8417_R0_0_I2 /\ e2aAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv8417_R0_0_I2 /\ e2bAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv8417_R0_0_I2 /\ e3aAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv8417_R0_0_I2 /\ e3bAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv8417_R0_0_I2 /\ e4aAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv8417_R0_0_I2 /\ e4bAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv8417_R0_0_I2 /\ w1aAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv4429_R1_0_I2 /\ Inv8417_R0_0_I2 /\ w1bAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,Inv4429_R1_0_I2,w1bAction,w1b,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,w2Action)
  <1>12. TypeOK /\ Inv4081_R1_1_I2 /\ Inv4491_R1_1_I2 /\ Inv8417_R0_0_I2 /\ w2Action => Inv8417_R0_0_I2'
       BY DEF TypeOK,Inv4081_R1_1_I2,Inv4491_R1_1_I2,w2Action,w2,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,csAction)
  <1>13. TypeOK /\ Inv8417_R0_0_I2 /\ csAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,csAction,cs,Inv8417_R0_0_I2
  \* (Inv8417_R0_0_I2,exitAction)
  <1>14. TypeOK /\ Inv8417_R0_0_I2 /\ exitAction => Inv8417_R0_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv8417_R0_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4429_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv4472_R2_0_I3 /\ Inv61_R2_0_I3 /\ Inv4429_R1_0_I2 /\ Next => Inv4429_R1_0_I2'
  \* (Inv4429_R1_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv4429_R1_0_I2 /\ ncsAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv4429_R1_0_I2 /\ e1aAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv4429_R1_0_I2 /\ e1bAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv4429_R1_0_I2 /\ e2aAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv4429_R1_0_I2 /\ e2bAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv4429_R1_0_I2 /\ e3aAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv4429_R1_0_I2 /\ e3bAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv4429_R1_0_I2 /\ e4aAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv4429_R1_0_I2 /\ e4bAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv4429_R1_0_I2 /\ w1aAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv4429_R1_0_I2 /\ w1bAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,w2Action)
  <1>12. TypeOK /\ Inv4472_R2_0_I3 /\ Inv61_R2_0_I3 /\ Inv4429_R1_0_I2 /\ w2Action => Inv4429_R1_0_I2'
       BY DEF TypeOK,Inv4472_R2_0_I3,Inv61_R2_0_I3,w2Action,w2,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,csAction)
  <1>13. TypeOK /\ Inv4429_R1_0_I2 /\ csAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,csAction,cs,Inv4429_R1_0_I2
  \* (Inv4429_R1_0_I2,exitAction)
  <1>14. TypeOK /\ Inv4429_R1_0_I2 /\ exitAction => Inv4429_R1_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv4429_R1_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4472_R2_0_I3
THEOREM L_4 == TypeOK /\ Inv2373_R5_0_I2 /\ Inv4472_R2_0_I3 /\ Next => Inv4472_R2_0_I3'
  \* (Inv4472_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv4472_R2_0_I3 /\ ncsAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,ncsAction,ncs,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv4472_R2_0_I3 /\ e1aAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e1aAction,e1a,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv4472_R2_0_I3 /\ e1bAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e1bAction,e1b,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv4472_R2_0_I3 /\ e2aAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e2aAction,e2a,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv4472_R2_0_I3 /\ e2bAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e2bAction,e2b,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv4472_R2_0_I3 /\ e3aAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e3aAction,e3a,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv4472_R2_0_I3 /\ e3bAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e3bAction,e3b,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv4472_R2_0_I3 /\ e4aAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e4aAction,e4a,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv4472_R2_0_I3 /\ e4bAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,e4bAction,e4b,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv2373_R5_0_I2 /\ Inv4472_R2_0_I3 /\ w1aAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,Inv2373_R5_0_I2,w1aAction,w1a,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv4472_R2_0_I3 /\ w1bAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,w1bAction,w1b,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv4472_R2_0_I3 /\ w2Action => Inv4472_R2_0_I3'
       BY DEF TypeOK,w2Action,w2,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv4472_R2_0_I3 /\ csAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,csAction,cs,Inv4472_R2_0_I3
  \* (Inv4472_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv4472_R2_0_I3 /\ exitAction => Inv4472_R2_0_I3'
       BY DEF TypeOK,exitAction,exit,Inv4472_R2_0_I3
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2373_R5_0_I2
THEOREM L_5 == TypeOK /\ Inv5016_R8_0_I3 /\ Inv2373_R5_0_I2 /\ Next => Inv2373_R5_0_I2'
  \* (Inv2373_R5_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv2373_R5_0_I2 /\ ncsAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv2373_R5_0_I2 /\ e1aAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv2373_R5_0_I2 /\ e1bAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv2373_R5_0_I2 /\ e2aAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv2373_R5_0_I2 /\ e2bAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv2373_R5_0_I2 /\ e3aAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv2373_R5_0_I2 /\ e3bAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv2373_R5_0_I2 /\ e4aAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv5016_R8_0_I3 /\ Inv2373_R5_0_I2 /\ e4bAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,Inv5016_R8_0_I3,e4bAction,e4b,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv2373_R5_0_I2 /\ w1aAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv2373_R5_0_I2 /\ w1bAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,w2Action)
  <1>12. TypeOK /\ Inv2373_R5_0_I2 /\ w2Action => Inv2373_R5_0_I2'
       BY DEF TypeOK,w2Action,w2,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,csAction)
  <1>13. TypeOK /\ Inv2373_R5_0_I2 /\ csAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,csAction,cs,Inv2373_R5_0_I2
  \* (Inv2373_R5_0_I2,exitAction)
  <1>14. TypeOK /\ Inv2373_R5_0_I2 /\ exitAction => Inv2373_R5_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv2373_R5_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv5016_R8_0_I3
THEOREM L_6 == TypeOK /\ Inv3258_R10_0_I3 /\ Inv61_R2_0_I3 /\ Inv5016_R8_0_I3 /\ Next => Inv5016_R8_0_I3'
  \* (Inv5016_R8_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv5016_R8_0_I3 /\ ncsAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,ncsAction,ncs,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv5016_R8_0_I3 /\ e1aAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e1aAction,e1a,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv5016_R8_0_I3 /\ e1bAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e1bAction,e1b,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv5016_R8_0_I3 /\ e2aAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e2aAction,e2a,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv5016_R8_0_I3 /\ e2bAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e2bAction,e2b,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv5016_R8_0_I3 /\ e3aAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e3aAction,e3a,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv3258_R10_0_I3 /\ Inv5016_R8_0_I3 /\ e3bAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,Inv3258_R10_0_I3,e3bAction,e3b,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv5016_R8_0_I3 /\ e4aAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e4aAction,e4a,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv5016_R8_0_I3 /\ e4bAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,e4bAction,e4b,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv5016_R8_0_I3 /\ w1aAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,w1aAction,w1a,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv5016_R8_0_I3 /\ w1bAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,w1bAction,w1b,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,w2Action)
  <1>12. TypeOK /\ Inv61_R2_0_I3 /\ Inv5016_R8_0_I3 /\ w2Action => Inv5016_R8_0_I3'
       BY DEF TypeOK,Inv61_R2_0_I3,w2Action,w2,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,csAction)
  <1>13. TypeOK /\ Inv5016_R8_0_I3 /\ csAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,csAction,cs,Inv5016_R8_0_I3
  \* (Inv5016_R8_0_I3,exitAction)
  <1>14. TypeOK /\ Inv5016_R8_0_I3 /\ exitAction => Inv5016_R8_0_I3'
       BY DEF TypeOK,exitAction,exit,Inv5016_R8_0_I3
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv3258_R10_0_I3
THEOREM L_7 == TypeOK /\ Inv1_R0_0_I0 /\ Inv3811_R12_1_I2 /\ Inv3811_R12_1_I2 /\ Inv3258_R10_0_I3 /\ Next => Inv3258_R10_0_I3'
  \* (Inv3258_R10_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv3258_R10_0_I3 /\ ncsAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,ncsAction,ncs,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv3258_R10_0_I3 /\ e1aAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e1aAction,e1a,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv3258_R10_0_I3 /\ e1bAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e1bAction,e1b,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv3258_R10_0_I3 /\ e2aAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e2aAction,e2a,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv1_R0_0_I0 /\ Inv3258_R10_0_I3 /\ e2bAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,Inv1_R0_0_I0,e2bAction,e2b,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv3258_R10_0_I3 /\ e3aAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e3aAction,e3a,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv3258_R10_0_I3 /\ e3bAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e3bAction,e3b,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv3258_R10_0_I3 /\ e4aAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e4aAction,e4a,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv3258_R10_0_I3 /\ e4bAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,e4bAction,e4b,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv3258_R10_0_I3 /\ w1aAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,w1aAction,w1a,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv3258_R10_0_I3 /\ w1bAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,w1bAction,w1b,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,w2Action)
  <1>12. TypeOK /\ Inv3811_R12_1_I2 /\ Inv3811_R12_1_I2 /\ Inv3258_R10_0_I3 /\ w2Action => Inv3258_R10_0_I3'
       BY DEF TypeOK,Inv3811_R12_1_I2,Inv3811_R12_1_I2,w2Action,w2,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,csAction)
  <1>13. TypeOK /\ Inv3258_R10_0_I3 /\ csAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,csAction,cs,Inv3258_R10_0_I3
  \* (Inv3258_R10_0_I3,exitAction)
  <1>14. TypeOK /\ Inv3258_R10_0_I3 /\ exitAction => Inv3258_R10_0_I3'
       BY DEF TypeOK,exitAction,exit,Inv3258_R10_0_I3
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1_R0_0_I0
THEOREM L_8 == TypeOK /\ Inv2073_R1_0_I4 /\ Inv1_R0_0_I0 /\ Next => Inv1_R0_0_I0'
  \* (Inv1_R0_0_I0,ncsAction)
  <1>1. TypeOK /\ Inv1_R0_0_I0 /\ ncsAction => Inv1_R0_0_I0'
       BY DEF TypeOK,ncsAction,ncs,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e1aAction)
  <1>2. TypeOK /\ Inv1_R0_0_I0 /\ e1aAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e1aAction,e1a,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e1bAction)
  <1>3. TypeOK /\ Inv1_R0_0_I0 /\ e1bAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e1bAction,e1b,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e2aAction)
  <1>4. TypeOK /\ Inv2073_R1_0_I4 /\ Inv1_R0_0_I0 /\ e2aAction => Inv1_R0_0_I0'
       BY DEF TypeOK,Inv2073_R1_0_I4,e2aAction,e2a,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e2bAction)
  <1>5. TypeOK /\ Inv1_R0_0_I0 /\ e2bAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e2bAction,e2b,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e3aAction)
  <1>6. TypeOK /\ Inv1_R0_0_I0 /\ e3aAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e3aAction,e3a,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e3bAction)
  <1>7. TypeOK /\ Inv1_R0_0_I0 /\ e3bAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e3bAction,e3b,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e4aAction)
  <1>8. TypeOK /\ Inv1_R0_0_I0 /\ e4aAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e4aAction,e4a,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,e4bAction)
  <1>9. TypeOK /\ Inv1_R0_0_I0 /\ e4bAction => Inv1_R0_0_I0'
       BY DEF TypeOK,e4bAction,e4b,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,w1aAction)
  <1>10. TypeOK /\ Inv1_R0_0_I0 /\ w1aAction => Inv1_R0_0_I0'
       BY DEF TypeOK,w1aAction,w1a,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,w1bAction)
  <1>11. TypeOK /\ Inv1_R0_0_I0 /\ w1bAction => Inv1_R0_0_I0'
       BY DEF TypeOK,w1bAction,w1b,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,w2Action)
  <1>12. TypeOK /\ Inv1_R0_0_I0 /\ w2Action => Inv1_R0_0_I0'
       BY DEF TypeOK,w2Action,w2,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,csAction)
  <1>13. TypeOK /\ Inv1_R0_0_I0 /\ csAction => Inv1_R0_0_I0'
       BY DEF TypeOK,csAction,cs,Inv1_R0_0_I0
  \* (Inv1_R0_0_I0,exitAction)
  <1>14. TypeOK /\ Inv1_R0_0_I0 /\ exitAction => Inv1_R0_0_I0'
       BY DEF TypeOK,exitAction,exit,Inv1_R0_0_I0
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2073_R1_0_I4
THEOREM L_9 == TypeOK /\ Inv4045_R14_0_I4 /\ Inv2073_R1_0_I4 /\ Next => Inv2073_R1_0_I4'
  \* (Inv2073_R1_0_I4,ncsAction)
  <1>1. TypeOK /\ Inv2073_R1_0_I4 /\ ncsAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,ncsAction,ncs,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e1aAction)
  <1>2. TypeOK /\ Inv2073_R1_0_I4 /\ e1aAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e1aAction,e1a,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e1bAction)
  <1>3. TypeOK /\ Inv2073_R1_0_I4 /\ e1bAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e1bAction,e1b,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e2aAction)
  <1>4. TypeOK /\ Inv2073_R1_0_I4 /\ e2aAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e2aAction,e2a,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e2bAction)
  <1>5. TypeOK /\ Inv2073_R1_0_I4 /\ e2bAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e2bAction,e2b,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e3aAction)
  <1>6. TypeOK /\ Inv2073_R1_0_I4 /\ e3aAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e3aAction,e3a,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e3bAction)
  <1>7. TypeOK /\ Inv2073_R1_0_I4 /\ e3bAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e3bAction,e3b,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e4aAction)
  <1>8. TypeOK /\ Inv2073_R1_0_I4 /\ e4aAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e4aAction,e4a,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,e4bAction)
  <1>9. TypeOK /\ Inv2073_R1_0_I4 /\ e4bAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,e4bAction,e4b,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,w1aAction)
  <1>10. TypeOK /\ Inv2073_R1_0_I4 /\ w1aAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,w1aAction,w1a,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,w1bAction)
  <1>11. TypeOK /\ Inv2073_R1_0_I4 /\ w1bAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,w1bAction,w1b,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,w2Action)
  <1>12. TypeOK /\ Inv4045_R14_0_I4 /\ Inv2073_R1_0_I4 /\ w2Action => Inv2073_R1_0_I4'
       BY DEF TypeOK,Inv4045_R14_0_I4,w2Action,w2,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,csAction)
  <1>13. TypeOK /\ Inv2073_R1_0_I4 /\ csAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,csAction,cs,Inv2073_R1_0_I4
  \* (Inv2073_R1_0_I4,exitAction)
  <1>14. TypeOK /\ Inv2073_R1_0_I4 /\ exitAction => Inv2073_R1_0_I4'
       BY DEF TypeOK,exitAction,exit,Inv2073_R1_0_I4
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4045_R14_0_I4
THEOREM L_10 == TypeOK /\ Inv11_R15_0_I1 /\ Inv4045_R14_0_I4 /\ Next => Inv4045_R14_0_I4'
  \* (Inv4045_R14_0_I4,ncsAction)
  <1>1. TypeOK /\ Inv4045_R14_0_I4 /\ ncsAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,ncsAction,ncs,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e1aAction)
  <1>2. TypeOK /\ Inv4045_R14_0_I4 /\ e1aAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e1aAction,e1a,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e1bAction)
  <1>3. TypeOK /\ Inv4045_R14_0_I4 /\ e1bAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e1bAction,e1b,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e2aAction)
  <1>4. TypeOK /\ Inv4045_R14_0_I4 /\ e2aAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e2aAction,e2a,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e2bAction)
  <1>5. TypeOK /\ Inv4045_R14_0_I4 /\ e2bAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e2bAction,e2b,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e3aAction)
  <1>6. TypeOK /\ Inv4045_R14_0_I4 /\ e3aAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e3aAction,e3a,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e3bAction)
  <1>7. TypeOK /\ Inv4045_R14_0_I4 /\ e3bAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e3bAction,e3b,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e4aAction)
  <1>8. TypeOK /\ Inv4045_R14_0_I4 /\ e4aAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e4aAction,e4a,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,e4bAction)
  <1>9. TypeOK /\ Inv4045_R14_0_I4 /\ e4bAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,e4bAction,e4b,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,w1aAction)
  <1>10. TypeOK /\ Inv11_R15_0_I1 /\ Inv4045_R14_0_I4 /\ w1aAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,Inv11_R15_0_I1,w1aAction,w1a,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,w1bAction)
  <1>11. TypeOK /\ Inv4045_R14_0_I4 /\ w1bAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,w1bAction,w1b,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,w2Action)
  <1>12. TypeOK /\ Inv4045_R14_0_I4 /\ w2Action => Inv4045_R14_0_I4'
       BY DEF TypeOK,w2Action,w2,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,csAction)
  <1>13. TypeOK /\ Inv4045_R14_0_I4 /\ csAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,csAction,cs,Inv4045_R14_0_I4
  \* (Inv4045_R14_0_I4,exitAction)
  <1>14. TypeOK /\ Inv4045_R14_0_I4 /\ exitAction => Inv4045_R14_0_I4'
       BY DEF TypeOK,exitAction,exit,Inv4045_R14_0_I4
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv11_R15_0_I1
THEOREM L_11 == TypeOK /\ Inv11_R15_0_I1 /\ Next => Inv11_R15_0_I1'
  \* (Inv11_R15_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv11_R15_0_I1 /\ ncsAction => Inv11_R15_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv11_R15_0_I1 /\ e1aAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e1aAction,e1a,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv11_R15_0_I1 /\ e1bAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e1bAction,e1b,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv11_R15_0_I1 /\ e2aAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e2aAction,e2a,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv11_R15_0_I1 /\ e2bAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e2bAction,e2b,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv11_R15_0_I1 /\ e3aAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e3aAction,e3a,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv11_R15_0_I1 /\ e3bAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e3bAction,e3b,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv11_R15_0_I1 /\ e4aAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e4aAction,e4a,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv11_R15_0_I1 /\ e4bAction => Inv11_R15_0_I1'
       BY DEF TypeOK,e4bAction,e4b,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv11_R15_0_I1 /\ w1aAction => Inv11_R15_0_I1'
       BY DEF TypeOK,w1aAction,w1a,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv11_R15_0_I1 /\ w1bAction => Inv11_R15_0_I1'
       BY DEF TypeOK,w1bAction,w1b,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,w2Action)
  <1>12. TypeOK /\ Inv11_R15_0_I1 /\ w2Action => Inv11_R15_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,csAction)
  <1>13. TypeOK /\ Inv11_R15_0_I1 /\ csAction => Inv11_R15_0_I1'
       BY DEF TypeOK,csAction,cs,Inv11_R15_0_I1
  \* (Inv11_R15_0_I1,exitAction)
  <1>14. TypeOK /\ Inv11_R15_0_I1 /\ exitAction => Inv11_R15_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv11_R15_0_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv3811_R12_1_I2
THEOREM L_12 == TypeOK /\ Inv36_R14_1_I1 /\ Inv3811_R12_1_I2 /\ Next => Inv3811_R12_1_I2'
  \* (Inv3811_R12_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv3811_R12_1_I2 /\ ncsAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv3811_R12_1_I2 /\ e1aAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv3811_R12_1_I2 /\ e1bAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv3811_R12_1_I2 /\ e2aAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv3811_R12_1_I2 /\ e2bAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv3811_R12_1_I2 /\ e3aAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv3811_R12_1_I2 /\ e3bAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv3811_R12_1_I2 /\ e4aAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv3811_R12_1_I2 /\ e4bAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv36_R14_1_I1 /\ Inv3811_R12_1_I2 /\ w1aAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,Inv36_R14_1_I1,w1aAction,w1a,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv3811_R12_1_I2 /\ w1bAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,w2Action)
  <1>12. TypeOK /\ Inv3811_R12_1_I2 /\ w2Action => Inv3811_R12_1_I2'
       BY DEF TypeOK,w2Action,w2,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,csAction)
  <1>13. TypeOK /\ Inv3811_R12_1_I2 /\ csAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,csAction,cs,Inv3811_R12_1_I2
  \* (Inv3811_R12_1_I2,exitAction)
  <1>14. TypeOK /\ Inv3811_R12_1_I2 /\ exitAction => Inv3811_R12_1_I2'
       BY DEF TypeOK,exitAction,exit,Inv3811_R12_1_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv36_R14_1_I1
THEOREM L_13 == TypeOK /\ Inv36_R14_1_I1 /\ Next => Inv36_R14_1_I1'
  \* (Inv36_R14_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv36_R14_1_I1 /\ ncsAction => Inv36_R14_1_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e1aAction)
  <1>2. TypeOK /\ Inv36_R14_1_I1 /\ e1aAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e1aAction,e1a,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e1bAction)
  <1>3. TypeOK /\ Inv36_R14_1_I1 /\ e1bAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e1bAction,e1b,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e2aAction)
  <1>4. TypeOK /\ Inv36_R14_1_I1 /\ e2aAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e2aAction,e2a,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e2bAction)
  <1>5. TypeOK /\ Inv36_R14_1_I1 /\ e2bAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e2bAction,e2b,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e3aAction)
  <1>6. TypeOK /\ Inv36_R14_1_I1 /\ e3aAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e3aAction,e3a,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e3bAction)
  <1>7. TypeOK /\ Inv36_R14_1_I1 /\ e3bAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e3bAction,e3b,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e4aAction)
  <1>8. TypeOK /\ Inv36_R14_1_I1 /\ e4aAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e4aAction,e4a,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,e4bAction)
  <1>9. TypeOK /\ Inv36_R14_1_I1 /\ e4bAction => Inv36_R14_1_I1'
       BY DEF TypeOK,e4bAction,e4b,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,w1aAction)
  <1>10. TypeOK /\ Inv36_R14_1_I1 /\ w1aAction => Inv36_R14_1_I1'
       BY DEF TypeOK,w1aAction,w1a,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,w1bAction)
  <1>11. TypeOK /\ Inv36_R14_1_I1 /\ w1bAction => Inv36_R14_1_I1'
       BY DEF TypeOK,w1bAction,w1b,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,w2Action)
  <1>12. TypeOK /\ Inv36_R14_1_I1 /\ w2Action => Inv36_R14_1_I1'
       BY DEF TypeOK,w2Action,w2,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,csAction)
  <1>13. TypeOK /\ Inv36_R14_1_I1 /\ csAction => Inv36_R14_1_I1'
       BY DEF TypeOK,csAction,cs,Inv36_R14_1_I1
  \* (Inv36_R14_1_I1,exitAction)
  <1>14. TypeOK /\ Inv36_R14_1_I1 /\ exitAction => Inv36_R14_1_I1'
       BY DEF TypeOK,exitAction,exit,Inv36_R14_1_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv61_R2_0_I3
THEOREM L_14 == TypeOK /\ Inv61_R2_0_I3 /\ Next => Inv61_R2_0_I3'
  \* (Inv61_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv61_R2_0_I3 /\ ncsAction => Inv61_R2_0_I3'
       BY DEF TypeOK,ncsAction,ncs,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv61_R2_0_I3 /\ e1aAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e1aAction,e1a,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv61_R2_0_I3 /\ e1bAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e1bAction,e1b,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv61_R2_0_I3 /\ e2aAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e2aAction,e2a,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv61_R2_0_I3 /\ e2bAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e2bAction,e2b,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv61_R2_0_I3 /\ e3aAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e3aAction,e3a,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv61_R2_0_I3 /\ e3bAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e3bAction,e3b,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv61_R2_0_I3 /\ e4aAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e4aAction,e4a,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv61_R2_0_I3 /\ e4bAction => Inv61_R2_0_I3'
       BY DEF TypeOK,e4bAction,e4b,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv61_R2_0_I3 /\ w1aAction => Inv61_R2_0_I3'
       BY DEF TypeOK,w1aAction,w1a,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv61_R2_0_I3 /\ w1bAction => Inv61_R2_0_I3'
       BY DEF TypeOK,w1bAction,w1b,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv61_R2_0_I3 /\ w2Action => Inv61_R2_0_I3'
       BY DEF TypeOK,w2Action,w2,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv61_R2_0_I3 /\ csAction => Inv61_R2_0_I3'
       BY DEF TypeOK,csAction,cs,Inv61_R2_0_I3
  \* (Inv61_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv61_R2_0_I3 /\ exitAction => Inv61_R2_0_I3'
       BY DEF TypeOK,exitAction,exit,Inv61_R2_0_I3
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4081_R1_1_I2
THEOREM L_15 == TypeOK /\ Inv6208_R3_0_I2 /\ Inv4081_R1_1_I2 /\ Next => Inv4081_R1_1_I2'
  \* (Inv4081_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv4081_R1_1_I2 /\ ncsAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv4081_R1_1_I2 /\ e1aAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv4081_R1_1_I2 /\ e1bAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv4081_R1_1_I2 /\ e2aAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv4081_R1_1_I2 /\ e2bAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv4081_R1_1_I2 /\ e3aAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv4081_R1_1_I2 /\ e3bAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv4081_R1_1_I2 /\ e4aAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv4081_R1_1_I2 /\ e4bAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv6208_R3_0_I2 /\ Inv4081_R1_1_I2 /\ w1aAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,Inv6208_R3_0_I2,w1aAction,w1a,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv4081_R1_1_I2 /\ w1bAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv4081_R1_1_I2 /\ w2Action => Inv4081_R1_1_I2'
       BY DEF TypeOK,w2Action,w2,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv4081_R1_1_I2 /\ csAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,csAction,cs,Inv4081_R1_1_I2
  \* (Inv4081_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv4081_R1_1_I2 /\ exitAction => Inv4081_R1_1_I2'
       BY DEF TypeOK,exitAction,exit,Inv4081_R1_1_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv6208_R3_0_I2
THEOREM L_16 == TypeOK /\ Inv1739_R7_0_I2 /\ Inv6208_R3_0_I2 /\ Next => Inv6208_R3_0_I2'
  \* (Inv6208_R3_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv6208_R3_0_I2 /\ ncsAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv6208_R3_0_I2 /\ e1aAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv6208_R3_0_I2 /\ e1bAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv6208_R3_0_I2 /\ e2aAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv6208_R3_0_I2 /\ e2bAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv6208_R3_0_I2 /\ e3aAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv6208_R3_0_I2 /\ e3bAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv6208_R3_0_I2 /\ e4aAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv1739_R7_0_I2 /\ Inv6208_R3_0_I2 /\ e4bAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,Inv1739_R7_0_I2,e4bAction,e4b,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv6208_R3_0_I2 /\ w1aAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv6208_R3_0_I2 /\ w1bAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,w2Action)
  <1>12. TypeOK /\ Inv6208_R3_0_I2 /\ w2Action => Inv6208_R3_0_I2'
       BY DEF TypeOK,w2Action,w2,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,csAction)
  <1>13. TypeOK /\ Inv6208_R3_0_I2 /\ csAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,csAction,cs,Inv6208_R3_0_I2
  \* (Inv6208_R3_0_I2,exitAction)
  <1>14. TypeOK /\ Inv6208_R3_0_I2 /\ exitAction => Inv6208_R3_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv6208_R3_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1739_R7_0_I2
THEOREM L_17 == TypeOK /\ Inv31710_R9_0_I2 /\ Inv1739_R7_0_I2 /\ Next => Inv1739_R7_0_I2'
  \* (Inv1739_R7_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv1739_R7_0_I2 /\ ncsAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv1739_R7_0_I2 /\ e1aAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv1739_R7_0_I2 /\ e1bAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv1739_R7_0_I2 /\ e2aAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv1739_R7_0_I2 /\ e2bAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv1739_R7_0_I2 /\ e3aAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv31710_R9_0_I2 /\ Inv1739_R7_0_I2 /\ e3bAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,Inv31710_R9_0_I2,e3bAction,e3b,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv1739_R7_0_I2 /\ e4aAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv1739_R7_0_I2 /\ e4bAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv1739_R7_0_I2 /\ w1aAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv1739_R7_0_I2 /\ w1bAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,w2Action)
  <1>12. TypeOK /\ Inv1739_R7_0_I2 /\ w2Action => Inv1739_R7_0_I2'
       BY DEF TypeOK,w2Action,w2,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,csAction)
  <1>13. TypeOK /\ Inv1739_R7_0_I2 /\ csAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,csAction,cs,Inv1739_R7_0_I2
  \* (Inv1739_R7_0_I2,exitAction)
  <1>14. TypeOK /\ Inv1739_R7_0_I2 /\ exitAction => Inv1739_R7_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv1739_R7_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv31710_R9_0_I2
THEOREM L_18 == TypeOK /\ Inv2883_R11_0_I3 /\ Inv31710_R9_0_I2 /\ Next => Inv31710_R9_0_I2'
  \* (Inv31710_R9_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv31710_R9_0_I2 /\ ncsAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv31710_R9_0_I2 /\ e1aAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv31710_R9_0_I2 /\ e1bAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv31710_R9_0_I2 /\ e2aAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv2883_R11_0_I3 /\ Inv31710_R9_0_I2 /\ e2bAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,Inv2883_R11_0_I3,e2bAction,e2b,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv31710_R9_0_I2 /\ e3aAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv31710_R9_0_I2 /\ e3bAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv31710_R9_0_I2 /\ e4aAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv31710_R9_0_I2 /\ e4bAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv31710_R9_0_I2 /\ w1aAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv31710_R9_0_I2 /\ w1bAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,w2Action)
  <1>12. TypeOK /\ Inv31710_R9_0_I2 /\ w2Action => Inv31710_R9_0_I2'
       BY DEF TypeOK,w2Action,w2,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,csAction)
  <1>13. TypeOK /\ Inv31710_R9_0_I2 /\ csAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,csAction,cs,Inv31710_R9_0_I2
  \* (Inv31710_R9_0_I2,exitAction)
  <1>14. TypeOK /\ Inv31710_R9_0_I2 /\ exitAction => Inv31710_R9_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv31710_R9_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2883_R11_0_I3
THEOREM L_19 == TypeOK /\ Inv2883_R11_0_I3 /\ Next => Inv2883_R11_0_I3'
  \* (Inv2883_R11_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv2883_R11_0_I3 /\ ncsAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,ncsAction,ncs,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv2883_R11_0_I3 /\ e1aAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e1aAction,e1a,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv2883_R11_0_I3 /\ e1bAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e1bAction,e1b,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv2883_R11_0_I3 /\ e2aAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e2aAction,e2a,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv2883_R11_0_I3 /\ e2bAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e2bAction,e2b,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv2883_R11_0_I3 /\ e3aAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e3aAction,e3a,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv2883_R11_0_I3 /\ e3bAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e3bAction,e3b,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv2883_R11_0_I3 /\ e4aAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e4aAction,e4a,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv2883_R11_0_I3 /\ e4bAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,e4bAction,e4b,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv2883_R11_0_I3 /\ w1aAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,w1aAction,w1a,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv2883_R11_0_I3 /\ w1bAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,w1bAction,w1b,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,w2Action)
  <1>12. TypeOK /\ Inv2883_R11_0_I3 /\ w2Action => Inv2883_R11_0_I3'
       BY DEF TypeOK,w2Action,w2,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,csAction)
  <1>13. TypeOK /\ Inv2883_R11_0_I3 /\ csAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,csAction,cs,Inv2883_R11_0_I3
  \* (Inv2883_R11_0_I3,exitAction)
  <1>14. TypeOK /\ Inv2883_R11_0_I3 /\ exitAction => Inv2883_R11_0_I3'
       BY DEF TypeOK,exitAction,exit,Inv2883_R11_0_I3
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4491_R1_1_I2
THEOREM L_20 == TypeOK /\ Inv4491_R1_1_I2 /\ Next => Inv4491_R1_1_I2'
  \* (Inv4491_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv4491_R1_1_I2 /\ ncsAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv4491_R1_1_I2 /\ e1aAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e1aAction,e1a,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv4491_R1_1_I2 /\ e1bAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e1bAction,e1b,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv4491_R1_1_I2 /\ e2aAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e2aAction,e2a,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv4491_R1_1_I2 /\ e2bAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e2bAction,e2b,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv4491_R1_1_I2 /\ e3aAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e3aAction,e3a,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv4491_R1_1_I2 /\ e3bAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e3bAction,e3b,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv4491_R1_1_I2 /\ e4aAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e4aAction,e4a,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv4491_R1_1_I2 /\ e4bAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,e4bAction,e4b,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv4491_R1_1_I2 /\ w1aAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,w1aAction,w1a,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv4491_R1_1_I2 /\ w1bAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,w1bAction,w1b,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv4491_R1_1_I2 /\ w2Action => Inv4491_R1_1_I2'
       BY DEF TypeOK,w2Action,w2,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv4491_R1_1_I2 /\ csAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,csAction,cs,Inv4491_R1_1_I2
  \* (Inv4491_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv4491_R1_1_I2 /\ exitAction => Inv4491_R1_1_I2'
       BY DEF TypeOK,exitAction,exit,Inv4491_R1_1_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20 DEF Next, IndGlobal



\* Inv21195_R4_0_I3 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARI] = "w1"))
=============================================================================
\* Modification History
\* Last modified Wed Apr 03 02:50:54 EDT 2024 by willyschultz
\* Last modified Tue Dec 18 13:48:46 PST 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
