------------------------------- MODULE Bakery_IndProofs -------------------------------
EXTENDS Bakery, FiniteSets, TLAPS, FiniteSetTheorems



\* Proof Graph Stats
\* ==================
\* seed: 2
\* num proof graph nodes: 20
\* num proof obligations: 280
Safety == H_MutualExclusion
Inv23439_af2b_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(pc[VARI] = "w1") \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARJ] = "cs"))
Inv3155_48f3_R1_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI})))
Inv21465_bb1b_R1_1_I2 == \A VARI \in Procs : (pc[VARI] = "e2") \/ ((pc[VARI] \in {"w1","w2"}) \/ ((unchecked[VARI] = {})))
Inv19891_1bc3_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] \in {"w1","w2"})) \/ (~(pc[VARJ] = "cs"))
Inv12452_548a_R1_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] \in {"w1","w2"}))
Inv4559_3f08_R1_1_I2 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "cs"))
Inv6938_a43e_R2_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(pc[VARJ] \in {"w1","w2"})))
Inv26_b6ff_R2_0_I3 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] \in {"w1","w2"}))
Inv1222_288c_R4_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "e4")))
Inv14061_f302_R7_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (max[VARJ] >= num[VARI]) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}) \/ (~(pc[VARJ] = "e3")) \/ (~(pc[VARI] \in {"w1","w2"})))
Inv11_73d9_R7_1_I1 == \A VARJ \in Procs : ~(num[VARJ] = 0) \/ (~(pc[VARJ] \in {"e4","w1","w2"}))
Inv10269_2818_R9_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e3") \/ (~(pc[VARJ] = "cs")))
Inv0_b3ba_R10_0_I0 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))
Inv5493_34f2_R10_1_I2 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3")) \/ (~(pc[VARI] = "w2")))
Inv2205_3e9d_R12_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ ((max[VARJ] >= num[VARI]) \/ (~(pc[VARJ] = "e2"))) \/ (~(pc[VARI] = "cs"))
Inv1_b58a_R13_0_I1 == \A VARI \in Procs : \A VARJ \in Procs : ((VARI \in unchecked[VARJ]) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARI] \in {"w1","w2"}))) \/ ((VARJ \in unchecked[VARI]))
Inv738_26ef_R13_1_I2 == \A VARI \in Procs : \A VARJ \in Procs : ((VARJ \in unchecked[nxt[VARJ]]) \/ ((max[nxt[VARJ]] >= num[VARJ]) \/ ((pc[VARI] = "e3")))) \/ (~(pc[VARJ] = "w2")) \/ (~((pc[nxt[VARJ]] = "e2")))
Inv296_b692_R14_1_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e3"))
Inv48_180c_R17_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e2"))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv23439_af2b_R0_0_I2
  /\ Inv3155_48f3_R1_0_I2
  /\ Inv6938_a43e_R2_0_I3
  /\ Inv14061_f302_R7_0_I3
  /\ Inv0_b3ba_R10_0_I0
  /\ Inv1_b58a_R13_0_I1
  /\ Inv738_26ef_R13_1_I2
  /\ Inv48_180c_R17_0_I1
  /\ Inv5493_34f2_R10_1_I2
  /\ Inv296_b692_R14_1_I1
  /\ Inv11_73d9_R7_1_I1
  /\ Inv26_b6ff_R2_0_I3
  /\ Inv21465_bb1b_R1_1_I2
  /\ Inv19891_1bc3_R1_1_I2
  /\ Inv1222_288c_R4_0_I2
  /\ Inv10269_2818_R9_0_I2
  /\ Inv2205_3e9d_R12_0_I3
  /\ Inv12452_548a_R1_1_I2
  /\ Inv4559_3f08_R1_1_I2


\* mean in-degree: 1.6
\* median in-degree: 2
\* max in-degree: 5
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == N \in Nat /\ Procs = 1..N /\ IsFiniteSet(Procs)

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
THEOREM L_1 == TypeOK /\ Inv23439_af2b_R0_0_I2 /\ Safety /\ Next => Safety'
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
  <1>7. TypeOK /\ Safety /\ e3bAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Safety,
                        TRUE,
                        NEW self \in Procs,
                        pc[self] = "e3",
                        NEW i \in {j \in Nat : j > max[self]},
                        num' = [num EXCEPT ![self] = i],
                        pc' = [pc EXCEPT ![self] = "e4"],
                        UNCHANGED << flag, unchecked, max, nxt >>
                 PROVE  Safety'
      BY DEF e3b, e3bAction
    <2> QED
      BY DEF TypeOK,e3bAction,e3b,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,e4aAction)
  <1>8. TypeOK /\ Safety /\ e4aAction => Safety' BY DEF TypeOK,e4aAction,e4a,Safety,\prec,H_MutualExclusion
  \* (Safety,e4bAction)
  <1>9. TypeOK /\ Safety /\ e4bAction => Safety' BY DEF TypeOK,e4bAction,e4b,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,w1aAction)
  <1>10. TypeOK /\ Safety /\ w1aAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Safety,
                        TRUE,
                        NEW self \in Procs,
                        pc[self] = "w1",
                        unchecked[self] # {},
                        NEW i \in unchecked[self],
                        nxt' = [nxt EXCEPT ![self] = i],
                        ~ flag[nxt'[self]],
                        pc' = [pc EXCEPT ![self] = "w2"],
                        UNCHANGED << num, flag, unchecked, max >>
                 PROVE  Safety'
      BY DEF w1a, w1aAction
    <2> QED
      BY DEF TypeOK,w1aAction,w1a,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,w1bAction)
  <1>11. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ Safety /\ w1bAction => Safety' BY DEF TypeOK,Inv23439_af2b_R0_0_I2,w1bAction,w1b,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,w2Action)
  <1>12. TypeOK /\ Safety /\ w2Action => Safety' BY DEF TypeOK,w2Action,w2,Safety,\prec,\prec,H_MutualExclusion
  \* (Safety,csAction)
  <1>13. TypeOK /\ Safety /\ csAction => Safety' BY DEF TypeOK,csAction,cs,Safety,\prec,H_MutualExclusion
  \* (Safety,exitAction)
  <1>14. TypeOK /\ Safety /\ exitAction => Safety' BY DEF TypeOK,exitAction,exit,Safety,\prec,H_MutualExclusion
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv23439_af2b_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv3155_48f3_R1_0_I2 /\ Inv21465_bb1b_R1_1_I2 /\ Inv19891_1bc3_R1_1_I2 /\ Inv12452_548a_R1_1_I2 /\ Inv4559_3f08_R1_1_I2 /\ Inv23439_af2b_R0_0_I2 /\ Next => Inv23439_af2b_R0_0_I2'
  <1>. USE A0
  \* (Inv23439_af2b_R0_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ ncsAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e1aAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e1bAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e2aAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv23439_af2b_R0_0_I2,\prec,Procs
  \* (Inv23439_af2b_R0_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e2bAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e3aAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e3bAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv23439_af2b_R0_0_I2,\prec,\prec
  \* (Inv23439_af2b_R0_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e4aAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ e4bAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv23439_af2b_R0_0_I2,\prec,\prec
  \* (Inv23439_af2b_R0_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ w1aAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv23439_af2b_R0_0_I2,\prec,\prec
  \* (Inv23439_af2b_R0_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ Inv23439_af2b_R0_0_I2 /\ w1bAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,Inv3155_48f3_R1_0_I2,w1bAction,w1b,Inv23439_af2b_R0_0_I2,\prec,\prec
  \* (Inv23439_af2b_R0_0_I2,w2Action)
  <1>12. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ Inv19891_1bc3_R1_1_I2 /\ Inv12452_548a_R1_1_I2 /\ Inv4559_3f08_R1_1_I2 /\ Inv23439_af2b_R0_0_I2 /\ w2Action => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,Inv21465_bb1b_R1_1_I2,Inv19891_1bc3_R1_1_I2,Inv12452_548a_R1_1_I2,Inv4559_3f08_R1_1_I2,w2Action,w2,Inv23439_af2b_R0_0_I2,\prec,\prec
  \* (Inv23439_af2b_R0_0_I2,csAction)
  <1>13. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ csAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,csAction,cs,Inv23439_af2b_R0_0_I2,\prec
  \* (Inv23439_af2b_R0_0_I2,exitAction)
  <1>14. TypeOK /\ Inv23439_af2b_R0_0_I2 /\ exitAction => Inv23439_af2b_R0_0_I2' BY DEF TypeOK,exitAction,exit,Inv23439_af2b_R0_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv3155_48f3_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv6938_a43e_R2_0_I3 /\ Inv26_b6ff_R2_0_I3 /\ Inv3155_48f3_R1_0_I2 /\ Next => Inv3155_48f3_R1_0_I2'
  <1>. USE A0
  \* (Inv3155_48f3_R1_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ ncsAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e1aAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e1bAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e2aAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv3155_48f3_R1_0_I2,\prec,Procs
  \* (Inv3155_48f3_R1_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e2bAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e3aAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e3bAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv3155_48f3_R1_0_I2,\prec,\prec
  \* (Inv3155_48f3_R1_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e4aAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ e4bAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv3155_48f3_R1_0_I2,\prec,\prec
  \* (Inv3155_48f3_R1_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ w1aAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv3155_48f3_R1_0_I2,\prec,\prec
  \* (Inv3155_48f3_R1_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ w1bAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,w1bAction,w1b,Inv3155_48f3_R1_0_I2,\prec,\prec
  \* (Inv3155_48f3_R1_0_I2,w2Action)
  <1>12. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ Inv26_b6ff_R2_0_I3 /\ Inv3155_48f3_R1_0_I2 /\ w2Action => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,Inv6938_a43e_R2_0_I3,Inv26_b6ff_R2_0_I3,w2Action,w2,Inv3155_48f3_R1_0_I2,\prec,\prec
  \* (Inv3155_48f3_R1_0_I2,csAction)
  <1>13. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ csAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,csAction,cs,Inv3155_48f3_R1_0_I2,\prec
  \* (Inv3155_48f3_R1_0_I2,exitAction)
  <1>14. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ exitAction => Inv3155_48f3_R1_0_I2' BY DEF TypeOK,exitAction,exit,Inv3155_48f3_R1_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv6938_a43e_R2_0_I3
THEOREM L_4 == TypeOK /\ Inv14061_f302_R7_0_I3 /\ Inv11_73d9_R7_1_I1 /\ Inv6938_a43e_R2_0_I3 /\ Next => Inv6938_a43e_R2_0_I3'
  <1>. USE A0
  \* (Inv6938_a43e_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ ncsAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e1aAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e1bAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e2aAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv6938_a43e_R2_0_I3,\prec,Procs
  \* (Inv6938_a43e_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e2bAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e3aAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv14061_f302_R7_0_I3 /\ Inv6938_a43e_R2_0_I3 /\ e3bAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,Inv14061_f302_R7_0_I3,e3bAction,e3b,Inv6938_a43e_R2_0_I3,\prec,\prec
  \* (Inv6938_a43e_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e4aAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ e4bAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv6938_a43e_R2_0_I3,\prec,\prec
  \* (Inv6938_a43e_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ w1aAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv6938_a43e_R2_0_I3,\prec,\prec
  \* (Inv6938_a43e_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ w1bAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv6938_a43e_R2_0_I3,\prec,\prec
  \* (Inv6938_a43e_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv11_73d9_R7_1_I1 /\ Inv6938_a43e_R2_0_I3 /\ w2Action => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,Inv11_73d9_R7_1_I1,w2Action,w2,Inv6938_a43e_R2_0_I3,\prec,\prec
  \* (Inv6938_a43e_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ csAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,csAction,cs,Inv6938_a43e_R2_0_I3,\prec
  \* (Inv6938_a43e_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ exitAction => Inv6938_a43e_R2_0_I3' BY DEF TypeOK,exitAction,exit,Inv6938_a43e_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv14061_f302_R7_0_I3
THEOREM L_5 == TypeOK /\ Inv0_b3ba_R10_0_I0 /\ Inv5493_34f2_R10_1_I2 /\ Inv14061_f302_R7_0_I3 /\ Next => Inv14061_f302_R7_0_I3'
  <1>. USE A0
  \* (Inv14061_f302_R7_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv14061_f302_R7_0_I3 /\ ncsAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e1aAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e1bAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e2aAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv14061_f302_R7_0_I3,\prec,Procs
  \* (Inv14061_f302_R7_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ Inv14061_f302_R7_0_I3 /\ e2bAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,Inv0_b3ba_R10_0_I0,e2bAction,e2b,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e3aAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e3bAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv14061_f302_R7_0_I3,\prec,\prec
  \* (Inv14061_f302_R7_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e4aAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv14061_f302_R7_0_I3 /\ e4bAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv14061_f302_R7_0_I3,\prec,\prec
  \* (Inv14061_f302_R7_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv14061_f302_R7_0_I3 /\ w1aAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv14061_f302_R7_0_I3,\prec,\prec
  \* (Inv14061_f302_R7_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv14061_f302_R7_0_I3 /\ w1bAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv14061_f302_R7_0_I3,\prec,\prec
  \* (Inv14061_f302_R7_0_I3,w2Action)
  <1>12. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ Inv14061_f302_R7_0_I3 /\ w2Action => Inv14061_f302_R7_0_I3' BY DEF TypeOK,Inv5493_34f2_R10_1_I2,w2Action,w2,Inv14061_f302_R7_0_I3,\prec,\prec
  \* (Inv14061_f302_R7_0_I3,csAction)
  <1>13. TypeOK /\ Inv14061_f302_R7_0_I3 /\ csAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,csAction,cs,Inv14061_f302_R7_0_I3,\prec
  \* (Inv14061_f302_R7_0_I3,exitAction)
  <1>14. TypeOK /\ Inv14061_f302_R7_0_I3 /\ exitAction => Inv14061_f302_R7_0_I3' BY DEF TypeOK,exitAction,exit,Inv14061_f302_R7_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv0_b3ba_R10_0_I0
THEOREM L_6 == TypeOK /\ Inv1_b58a_R13_0_I1 /\ Inv738_26ef_R13_1_I2 /\ Inv0_b3ba_R10_0_I0 /\ Next => Inv0_b3ba_R10_0_I0'
  <1>. USE A0
  \* (Inv0_b3ba_R10_0_I0,ncsAction)
  <1>1. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ ncsAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,ncsAction,ncs,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,e1aAction)
  <1>2. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e1aAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e1aAction,e1a,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,e1bAction)
  <1>3. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e1bAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e1bAction,e1b,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,e2aAction)
  <1>4. TypeOK /\ Inv1_b58a_R13_0_I1 /\ Inv0_b3ba_R10_0_I0 /\ e2aAction => Inv0_b3ba_R10_0_I0' 
    <2> SUFFICES ASSUME TypeOK /\ Inv1_b58a_R13_0_I1 /\ Inv0_b3ba_R10_0_I0 /\ e2aAction,
                        NEW VARI \in Procs',
                        NEW VARJ \in Procs'
                 PROVE  ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))'
      BY DEF Inv0_b3ba_R10_0_I0
    <2> QED
      <3> SUFFICES ASSUME NEW self \in Procs,
                          pc[self] = "e2",
                          unchecked[self] # {},
                          NEW i \in unchecked[self],
                          /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                          /\ IF num[i] > max[self]
                              THEN /\ max' = [max EXCEPT ![self] = num[i]]
                              ELSE /\ max' = max,
                          pc' = [pc EXCEPT ![self] = "e2"],
                          UNCHANGED << num, flag, nxt >>
                   PROVE  ((VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"})))'
        BY DEF e2a, e2aAction
      <3> QED
        BY DEF TypeOK,Inv1_b58a_R13_0_I1,e2aAction,e2a,Inv0_b3ba_R10_0_I0,\prec,Procs
      
  \* (Inv0_b3ba_R10_0_I0,e2bAction)
  <1>5. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e2bAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e2bAction,e2b,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,e3aAction)
  <1>6. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e3aAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e3aAction,e3a,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,e3bAction)
  <1>7. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e3bAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e3bAction,e3b,Inv0_b3ba_R10_0_I0,\prec,\prec
  \* (Inv0_b3ba_R10_0_I0,e4aAction)
  <1>8. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e4aAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e4aAction,e4a,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,e4bAction)
  <1>9. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ e4bAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,e4bAction,e4b,Inv0_b3ba_R10_0_I0,\prec,\prec
  \* (Inv0_b3ba_R10_0_I0,w1aAction)
  <1>10. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ w1aAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,w1aAction,w1a,Inv0_b3ba_R10_0_I0,\prec,\prec
  \* (Inv0_b3ba_R10_0_I0,w1bAction)
  <1>11. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ w1bAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,w1bAction,w1b,Inv0_b3ba_R10_0_I0,\prec,\prec
  \* (Inv0_b3ba_R10_0_I0,w2Action)
  <1>12. TypeOK /\ Inv738_26ef_R13_1_I2 /\ Inv0_b3ba_R10_0_I0 /\ w2Action => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,Inv738_26ef_R13_1_I2,w2Action,w2,Inv0_b3ba_R10_0_I0,\prec,\prec
  \* (Inv0_b3ba_R10_0_I0,csAction)
  <1>13. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ csAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,csAction,cs,Inv0_b3ba_R10_0_I0,\prec
  \* (Inv0_b3ba_R10_0_I0,exitAction)
  <1>14. TypeOK /\ Inv0_b3ba_R10_0_I0 /\ exitAction => Inv0_b3ba_R10_0_I0' BY DEF TypeOK,exitAction,exit,Inv0_b3ba_R10_0_I0,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1_b58a_R13_0_I1
THEOREM L_7 == TypeOK /\ Inv738_26ef_R13_1_I2 /\ Inv1_b58a_R13_0_I1 /\ Next => Inv1_b58a_R13_0_I1'
  <1>. USE A0
  \* (Inv1_b58a_R13_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1_b58a_R13_0_I1 /\ ncsAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,ncsAction,ncs,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e1aAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e1aAction,e1a,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e1bAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e1bAction,e1b,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e2aAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e2aAction,e2a,Inv1_b58a_R13_0_I1,\prec,Procs
  \* (Inv1_b58a_R13_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e2bAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e2bAction,e2b,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e3aAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e3aAction,e3a,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e3bAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e3bAction,e3b,Inv1_b58a_R13_0_I1,\prec,\prec
  \* (Inv1_b58a_R13_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e4aAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e4aAction,e4a,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv1_b58a_R13_0_I1 /\ e4bAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,e4bAction,e4b,Inv1_b58a_R13_0_I1,\prec,\prec
  \* (Inv1_b58a_R13_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv1_b58a_R13_0_I1 /\ w1aAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,w1aAction,w1a,Inv1_b58a_R13_0_I1,\prec,\prec
  \* (Inv1_b58a_R13_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv1_b58a_R13_0_I1 /\ w1bAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,w1bAction,w1b,Inv1_b58a_R13_0_I1,\prec,\prec
  \* (Inv1_b58a_R13_0_I1,w2Action)
  <1>12. TypeOK /\ Inv738_26ef_R13_1_I2 /\ Inv1_b58a_R13_0_I1 /\ w2Action => Inv1_b58a_R13_0_I1' BY DEF TypeOK,Inv738_26ef_R13_1_I2,w2Action,w2,Inv1_b58a_R13_0_I1,\prec,\prec
  \* (Inv1_b58a_R13_0_I1,csAction)
  <1>13. TypeOK /\ Inv1_b58a_R13_0_I1 /\ csAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,csAction,cs,Inv1_b58a_R13_0_I1,\prec
  \* (Inv1_b58a_R13_0_I1,exitAction)
  <1>14. TypeOK /\ Inv1_b58a_R13_0_I1 /\ exitAction => Inv1_b58a_R13_0_I1' BY DEF TypeOK,exitAction,exit,Inv1_b58a_R13_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv738_26ef_R13_1_I2
THEOREM L_8 == TypeOK /\ Inv48_180c_R17_0_I1 /\ Inv738_26ef_R13_1_I2 /\ Next => Inv738_26ef_R13_1_I2'
  <1>. USE A0
  \* (Inv738_26ef_R13_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv738_26ef_R13_1_I2 /\ ncsAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e1aAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e1bAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e2aAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv738_26ef_R13_1_I2,\prec,Procs
  \* (Inv738_26ef_R13_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e2bAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e3aAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e3bAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv738_26ef_R13_1_I2,\prec,\prec
  \* (Inv738_26ef_R13_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e4aAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv738_26ef_R13_1_I2 /\ e4bAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv738_26ef_R13_1_I2,\prec,\prec
  \* (Inv738_26ef_R13_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv48_180c_R17_0_I1 /\ Inv738_26ef_R13_1_I2 /\ w1aAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,Inv48_180c_R17_0_I1,w1aAction,w1a,Inv738_26ef_R13_1_I2,\prec,\prec
  \* (Inv738_26ef_R13_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv738_26ef_R13_1_I2 /\ w1bAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,w1bAction,w1b,Inv738_26ef_R13_1_I2,\prec,\prec
  \* (Inv738_26ef_R13_1_I2,w2Action)
  <1>12. TypeOK /\ Inv738_26ef_R13_1_I2 /\ w2Action => Inv738_26ef_R13_1_I2' BY DEF TypeOK,w2Action,w2,Inv738_26ef_R13_1_I2,\prec,\prec
  \* (Inv738_26ef_R13_1_I2,csAction)
  <1>13. TypeOK /\ Inv738_26ef_R13_1_I2 /\ csAction => Inv738_26ef_R13_1_I2' BY DEF TypeOK,csAction,cs,Inv738_26ef_R13_1_I2,\prec
  \* (Inv738_26ef_R13_1_I2,exitAction)
  <1>14. TypeOK /\ Inv738_26ef_R13_1_I2 /\ exitAction => Inv738_26ef_R13_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv738_26ef_R13_1_I2,
                        TRUE,
                        NEW self \in Procs,
                        pc[self] = "exit",
                        UNCHANGED << flag, unchecked, max, nxt >>,
                        NEW VARI \in Procs',
                        NEW VARJ \in Procs',
                        \/ /\ \E k \in Nat:
                                num' = [num EXCEPT ![self] = k]
                           /\ pc' = [pc EXCEPT ![self] = "exit"]
                        \/ /\ num' = [num EXCEPT ![self] = 0]
                           /\ pc' = [pc EXCEPT ![self] = "ncs"]
                 PROVE  (((VARJ \in unchecked[nxt[VARJ]]) \/ ((max[nxt[VARJ]] >= num[VARJ]) \/ ((pc[VARI] = "e3")))) \/ (~(pc[VARJ] = "w2")) \/ (~((pc[nxt[VARJ]] = "e2"))))'
      BY DEF Inv738_26ef_R13_1_I2, exit, exitAction
    <2>1. CASE /\ \E k \in Nat:
                    num' = [num EXCEPT ![self] = k]
               /\ pc' = [pc EXCEPT ![self] = "exit"]
      BY <2>1 DEF TypeOK,exitAction,exit,Inv738_26ef_R13_1_I2,\prec
    <2>2. CASE /\ num' = [num EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
      BY <2>2 DEF TypeOK,exitAction,exit,Inv738_26ef_R13_1_I2,\prec
    <2>3. QED
      BY <2>1, <2>2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv48_180c_R17_0_I1
THEOREM L_9 == TypeOK /\ Inv48_180c_R17_0_I1 /\ Next => Inv48_180c_R17_0_I1'
  <1>. USE A0
  \* (Inv48_180c_R17_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv48_180c_R17_0_I1 /\ ncsAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,ncsAction,ncs,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,e1aAction)
  <1>2. TypeOK /\ Inv48_180c_R17_0_I1 /\ e1aAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e1aAction,e1a,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,e1bAction)
  <1>3. TypeOK /\ Inv48_180c_R17_0_I1 /\ e1bAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e1bAction,e1b,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,e2aAction)
  <1>4. TypeOK /\ Inv48_180c_R17_0_I1 /\ e2aAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e2aAction,e2a,Inv48_180c_R17_0_I1,\prec,Procs
  \* (Inv48_180c_R17_0_I1,e2bAction)
  <1>5. TypeOK /\ Inv48_180c_R17_0_I1 /\ e2bAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e2bAction,e2b,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,e3aAction)
  <1>6. TypeOK /\ Inv48_180c_R17_0_I1 /\ e3aAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e3aAction,e3a,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,e3bAction)
  <1>7. TypeOK /\ Inv48_180c_R17_0_I1 /\ e3bAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e3bAction,e3b,Inv48_180c_R17_0_I1,\prec,\prec
  \* (Inv48_180c_R17_0_I1,e4aAction)
  <1>8. TypeOK /\ Inv48_180c_R17_0_I1 /\ e4aAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e4aAction,e4a,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,e4bAction)
  <1>9. TypeOK /\ Inv48_180c_R17_0_I1 /\ e4bAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,e4bAction,e4b,Inv48_180c_R17_0_I1,\prec,\prec
  \* (Inv48_180c_R17_0_I1,w1aAction)
  <1>10. TypeOK /\ Inv48_180c_R17_0_I1 /\ w1aAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,w1aAction,w1a,Inv48_180c_R17_0_I1,\prec,\prec
  \* (Inv48_180c_R17_0_I1,w1bAction)
  <1>11. TypeOK /\ Inv48_180c_R17_0_I1 /\ w1bAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,w1bAction,w1b,Inv48_180c_R17_0_I1,\prec,\prec
  \* (Inv48_180c_R17_0_I1,w2Action)
  <1>12. TypeOK /\ Inv48_180c_R17_0_I1 /\ w2Action => Inv48_180c_R17_0_I1' BY DEF TypeOK,w2Action,w2,Inv48_180c_R17_0_I1,\prec,\prec
  \* (Inv48_180c_R17_0_I1,csAction)
  <1>13. TypeOK /\ Inv48_180c_R17_0_I1 /\ csAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,csAction,cs,Inv48_180c_R17_0_I1,\prec
  \* (Inv48_180c_R17_0_I1,exitAction)
  <1>14. TypeOK /\ Inv48_180c_R17_0_I1 /\ exitAction => Inv48_180c_R17_0_I1' BY DEF TypeOK,exitAction,exit,Inv48_180c_R17_0_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv5493_34f2_R10_1_I2
THEOREM L_10 == TypeOK /\ Inv738_26ef_R13_1_I2 /\ Inv296_b692_R14_1_I1 /\ Inv5493_34f2_R10_1_I2 /\ Next => Inv5493_34f2_R10_1_I2'
  <1>. USE A0
  \* (Inv5493_34f2_R10_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ ncsAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e1aAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e1bAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e2aAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv5493_34f2_R10_1_I2,\prec,Procs
  \* (Inv5493_34f2_R10_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv738_26ef_R13_1_I2 /\ Inv5493_34f2_R10_1_I2 /\ e2bAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,Inv738_26ef_R13_1_I2,e2bAction,e2b,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e3aAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e3bAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv5493_34f2_R10_1_I2,\prec,\prec
  \* (Inv5493_34f2_R10_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e4aAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ e4bAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv5493_34f2_R10_1_I2,\prec,\prec
  \* (Inv5493_34f2_R10_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv296_b692_R14_1_I1 /\ Inv5493_34f2_R10_1_I2 /\ w1aAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,Inv296_b692_R14_1_I1,w1aAction,w1a,Inv5493_34f2_R10_1_I2,\prec,\prec
  \* (Inv5493_34f2_R10_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ w1bAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,w1bAction,w1b,Inv5493_34f2_R10_1_I2,\prec,\prec
  \* (Inv5493_34f2_R10_1_I2,w2Action)
  <1>12. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ w2Action => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,w2Action,w2,Inv5493_34f2_R10_1_I2,\prec,\prec
  \* (Inv5493_34f2_R10_1_I2,csAction)
  <1>13. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ csAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,csAction,cs,Inv5493_34f2_R10_1_I2,\prec
  \* (Inv5493_34f2_R10_1_I2,exitAction)
  <1>14. TypeOK /\ Inv5493_34f2_R10_1_I2 /\ exitAction => Inv5493_34f2_R10_1_I2' BY DEF TypeOK,exitAction,exit,Inv5493_34f2_R10_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv296_b692_R14_1_I1
THEOREM L_11 == TypeOK /\ Inv48_180c_R17_0_I1 /\ Inv296_b692_R14_1_I1 /\ Next => Inv296_b692_R14_1_I1'
  <1>. USE A0
  \* (Inv296_b692_R14_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv296_b692_R14_1_I1 /\ ncsAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,ncsAction,ncs,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,e1aAction)
  <1>2. TypeOK /\ Inv296_b692_R14_1_I1 /\ e1aAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e1aAction,e1a,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,e1bAction)
  <1>3. TypeOK /\ Inv296_b692_R14_1_I1 /\ e1bAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e1bAction,e1b,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,e2aAction)
  <1>4. TypeOK /\ Inv296_b692_R14_1_I1 /\ e2aAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e2aAction,e2a,Inv296_b692_R14_1_I1,\prec,Procs
  \* (Inv296_b692_R14_1_I1,e2bAction)
  <1>5. TypeOK /\ Inv48_180c_R17_0_I1 /\ Inv296_b692_R14_1_I1 /\ e2bAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,Inv48_180c_R17_0_I1,e2bAction,e2b,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,e3aAction)
  <1>6. TypeOK /\ Inv296_b692_R14_1_I1 /\ e3aAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e3aAction,e3a,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,e3bAction)
  <1>7. TypeOK /\ Inv296_b692_R14_1_I1 /\ e3bAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e3bAction,e3b,Inv296_b692_R14_1_I1,\prec,\prec
  \* (Inv296_b692_R14_1_I1,e4aAction)
  <1>8. TypeOK /\ Inv296_b692_R14_1_I1 /\ e4aAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e4aAction,e4a,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,e4bAction)
  <1>9. TypeOK /\ Inv296_b692_R14_1_I1 /\ e4bAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,e4bAction,e4b,Inv296_b692_R14_1_I1,\prec,\prec
  \* (Inv296_b692_R14_1_I1,w1aAction)
  <1>10. TypeOK /\ Inv296_b692_R14_1_I1 /\ w1aAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,w1aAction,w1a,Inv296_b692_R14_1_I1,\prec,\prec
  \* (Inv296_b692_R14_1_I1,w1bAction)
  <1>11. TypeOK /\ Inv296_b692_R14_1_I1 /\ w1bAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,w1bAction,w1b,Inv296_b692_R14_1_I1,\prec,\prec
  \* (Inv296_b692_R14_1_I1,w2Action)
  <1>12. TypeOK /\ Inv296_b692_R14_1_I1 /\ w2Action => Inv296_b692_R14_1_I1' BY DEF TypeOK,w2Action,w2,Inv296_b692_R14_1_I1,\prec,\prec
  \* (Inv296_b692_R14_1_I1,csAction)
  <1>13. TypeOK /\ Inv296_b692_R14_1_I1 /\ csAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,csAction,cs,Inv296_b692_R14_1_I1,\prec
  \* (Inv296_b692_R14_1_I1,exitAction)
  <1>14. TypeOK /\ Inv296_b692_R14_1_I1 /\ exitAction => Inv296_b692_R14_1_I1' BY DEF TypeOK,exitAction,exit,Inv296_b692_R14_1_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv11_73d9_R7_1_I1
THEOREM L_12 == TypeOK /\ Inv11_73d9_R7_1_I1 /\ Next => Inv11_73d9_R7_1_I1'
  <1>. USE A0
  \* (Inv11_73d9_R7_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv11_73d9_R7_1_I1 /\ ncsAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,ncsAction,ncs,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,e1aAction)
  <1>2. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e1aAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e1aAction,e1a,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,e1bAction)
  <1>3. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e1bAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e1bAction,e1b,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,e2aAction)
  <1>4. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e2aAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e2aAction,e2a,Inv11_73d9_R7_1_I1,\prec,Procs
  \* (Inv11_73d9_R7_1_I1,e2bAction)
  <1>5. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e2bAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e2bAction,e2b,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,e3aAction)
  <1>6. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e3aAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e3aAction,e3a,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,e3bAction)
  <1>7. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e3bAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e3bAction,e3b,Inv11_73d9_R7_1_I1,\prec,\prec
  \* (Inv11_73d9_R7_1_I1,e4aAction)
  <1>8. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e4aAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e4aAction,e4a,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,e4bAction)
  <1>9. TypeOK /\ Inv11_73d9_R7_1_I1 /\ e4bAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,e4bAction,e4b,Inv11_73d9_R7_1_I1,\prec,\prec
  \* (Inv11_73d9_R7_1_I1,w1aAction)
  <1>10. TypeOK /\ Inv11_73d9_R7_1_I1 /\ w1aAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,w1aAction,w1a,Inv11_73d9_R7_1_I1,\prec,\prec
  \* (Inv11_73d9_R7_1_I1,w1bAction)
  <1>11. TypeOK /\ Inv11_73d9_R7_1_I1 /\ w1bAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,w1bAction,w1b,Inv11_73d9_R7_1_I1,\prec,\prec
  \* (Inv11_73d9_R7_1_I1,w2Action)
  <1>12. TypeOK /\ Inv11_73d9_R7_1_I1 /\ w2Action => Inv11_73d9_R7_1_I1' BY DEF TypeOK,w2Action,w2,Inv11_73d9_R7_1_I1,\prec,\prec
  \* (Inv11_73d9_R7_1_I1,csAction)
  <1>13. TypeOK /\ Inv11_73d9_R7_1_I1 /\ csAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,csAction,cs,Inv11_73d9_R7_1_I1,\prec
  \* (Inv11_73d9_R7_1_I1,exitAction)
  <1>14. TypeOK /\ Inv11_73d9_R7_1_I1 /\ exitAction => Inv11_73d9_R7_1_I1' BY DEF TypeOK,exitAction,exit,Inv11_73d9_R7_1_I1,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv26_b6ff_R2_0_I3
THEOREM L_13 == TypeOK /\ Inv11_73d9_R7_1_I1 /\ Inv26_b6ff_R2_0_I3 /\ Next => Inv26_b6ff_R2_0_I3'
  <1>. USE A0
  \* (Inv26_b6ff_R2_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ ncsAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e1aAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e1bAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e2aAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv26_b6ff_R2_0_I3,\prec,Procs
  \* (Inv26_b6ff_R2_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e2bAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e3aAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e3bAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv26_b6ff_R2_0_I3,\prec,\prec
  \* (Inv26_b6ff_R2_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ e4aAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv11_73d9_R7_1_I1 /\ Inv26_b6ff_R2_0_I3 /\ e4bAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,Inv11_73d9_R7_1_I1,e4bAction,e4b,Inv26_b6ff_R2_0_I3,\prec,\prec
  \* (Inv26_b6ff_R2_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ w1aAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv26_b6ff_R2_0_I3,\prec,\prec
  \* (Inv26_b6ff_R2_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ w1bAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,w1bAction,w1b,Inv26_b6ff_R2_0_I3,\prec,\prec
  \* (Inv26_b6ff_R2_0_I3,w2Action)
  <1>12. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ w2Action => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,w2Action,w2,Inv26_b6ff_R2_0_I3,\prec,\prec
  \* (Inv26_b6ff_R2_0_I3,csAction)
  <1>13. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ csAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,csAction,cs,Inv26_b6ff_R2_0_I3,\prec
  \* (Inv26_b6ff_R2_0_I3,exitAction)
  <1>14. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ exitAction => Inv26_b6ff_R2_0_I3' BY DEF TypeOK,exitAction,exit,Inv26_b6ff_R2_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv21465_bb1b_R1_1_I2
THEOREM L_14 == TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ Next => Inv21465_bb1b_R1_1_I2'
  <1>. USE A0
  \* (Inv21465_bb1b_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ ncsAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e1aAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e1bAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e2aAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv21465_bb1b_R1_1_I2,\prec,Procs
  \* (Inv21465_bb1b_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e2bAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e3aAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e3bAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv21465_bb1b_R1_1_I2,\prec,\prec
  \* (Inv21465_bb1b_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e4aAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ e4bAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv21465_bb1b_R1_1_I2,\prec,\prec
  \* (Inv21465_bb1b_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ w1aAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,Inv21465_bb1b_R1_1_I2,\prec,\prec
  \* (Inv21465_bb1b_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ w1bAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,w1bAction,w1b,Inv21465_bb1b_R1_1_I2,\prec,\prec
  \* (Inv21465_bb1b_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ w2Action => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv21465_bb1b_R1_1_I2,\prec,\prec
  \* (Inv21465_bb1b_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ csAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv21465_bb1b_R1_1_I2,\prec
  \* (Inv21465_bb1b_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ exitAction => Inv21465_bb1b_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv21465_bb1b_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv19891_1bc3_R1_1_I2
THEOREM L_15 == TypeOK /\ Inv1222_288c_R4_0_I2 /\ Inv6938_a43e_R2_0_I3 /\ Inv19891_1bc3_R1_1_I2 /\ Next => Inv19891_1bc3_R1_1_I2'
  <1>. USE A0
  \* (Inv19891_1bc3_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ ncsAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e1aAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e1bAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e2aAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv19891_1bc3_R1_1_I2,\prec,Procs
  \* (Inv19891_1bc3_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e2bAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e3aAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e3bAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv19891_1bc3_R1_1_I2,\prec,\prec
  \* (Inv19891_1bc3_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ e4aAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv1222_288c_R4_0_I2 /\ Inv19891_1bc3_R1_1_I2 /\ e4bAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,Inv1222_288c_R4_0_I2,e4bAction,e4b,Inv19891_1bc3_R1_1_I2,\prec,\prec
  \* (Inv19891_1bc3_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ w1aAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,Inv19891_1bc3_R1_1_I2,\prec,\prec
  \* (Inv19891_1bc3_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ Inv19891_1bc3_R1_1_I2 /\ w1bAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,Inv6938_a43e_R2_0_I3,w1bAction,w1b,Inv19891_1bc3_R1_1_I2,\prec,\prec
  \* (Inv19891_1bc3_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ w2Action => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv19891_1bc3_R1_1_I2,\prec,\prec
  \* (Inv19891_1bc3_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ csAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv19891_1bc3_R1_1_I2,\prec
  \* (Inv19891_1bc3_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv19891_1bc3_R1_1_I2 /\ exitAction => Inv19891_1bc3_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv19891_1bc3_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1222_288c_R4_0_I2
THEOREM L_16 == TypeOK /\ Inv10269_2818_R9_0_I2 /\ Inv6938_a43e_R2_0_I3 /\ Inv1222_288c_R4_0_I2 /\ Next => Inv1222_288c_R4_0_I2'
  <1>. USE A0
  \* (Inv1222_288c_R4_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv1222_288c_R4_0_I2 /\ ncsAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e1aAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e1bAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e2aAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv1222_288c_R4_0_I2,\prec,Procs
  \* (Inv1222_288c_R4_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e2bAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e2bAction,e2b,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e3aAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv10269_2818_R9_0_I2 /\ Inv1222_288c_R4_0_I2 /\ e3bAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,Inv10269_2818_R9_0_I2,e3bAction,e3b,Inv1222_288c_R4_0_I2,\prec,\prec
  \* (Inv1222_288c_R4_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e4aAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv1222_288c_R4_0_I2 /\ e4bAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv1222_288c_R4_0_I2,\prec,\prec
  \* (Inv1222_288c_R4_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv1222_288c_R4_0_I2 /\ w1aAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv1222_288c_R4_0_I2,\prec,\prec
  \* (Inv1222_288c_R4_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv6938_a43e_R2_0_I3 /\ Inv1222_288c_R4_0_I2 /\ w1bAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,Inv6938_a43e_R2_0_I3,w1bAction,w1b,Inv1222_288c_R4_0_I2,\prec,\prec
  \* (Inv1222_288c_R4_0_I2,w2Action)
  <1>12. TypeOK /\ Inv1222_288c_R4_0_I2 /\ w2Action => Inv1222_288c_R4_0_I2' BY DEF TypeOK,w2Action,w2,Inv1222_288c_R4_0_I2,\prec,\prec
  \* (Inv1222_288c_R4_0_I2,csAction)
  <1>13. TypeOK /\ Inv1222_288c_R4_0_I2 /\ csAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,csAction,cs,Inv1222_288c_R4_0_I2,\prec
  \* (Inv1222_288c_R4_0_I2,exitAction)
  <1>14. TypeOK /\ Inv1222_288c_R4_0_I2 /\ exitAction => Inv1222_288c_R4_0_I2' BY DEF TypeOK,exitAction,exit,Inv1222_288c_R4_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv10269_2818_R9_0_I2
THEOREM L_17 == TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ Inv14061_f302_R7_0_I3 /\ Inv10269_2818_R9_0_I2 /\ Next => Inv10269_2818_R9_0_I2'
  <1>. USE A0
  \* (Inv10269_2818_R9_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv10269_2818_R9_0_I2 /\ ncsAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,ncsAction,ncs,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,e1aAction)
  <1>2. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e1aAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e1aAction,e1a,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,e1bAction)
  <1>3. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e1bAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e1bAction,e1b,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,e2aAction)
  <1>4. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e2aAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e2aAction,e2a,Inv10269_2818_R9_0_I2,\prec,Procs
  \* (Inv10269_2818_R9_0_I2,e2bAction)
  <1>5. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ Inv10269_2818_R9_0_I2 /\ e2bAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,Inv2205_3e9d_R12_0_I3,e2bAction,e2b,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,e3aAction)
  <1>6. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e3aAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e3aAction,e3a,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,e3bAction)
  <1>7. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e3bAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e3bAction,e3b,Inv10269_2818_R9_0_I2,\prec,\prec
  \* (Inv10269_2818_R9_0_I2,e4aAction)
  <1>8. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e4aAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e4aAction,e4a,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,e4bAction)
  <1>9. TypeOK /\ Inv10269_2818_R9_0_I2 /\ e4bAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,e4bAction,e4b,Inv10269_2818_R9_0_I2,\prec,\prec
  \* (Inv10269_2818_R9_0_I2,w1aAction)
  <1>10. TypeOK /\ Inv10269_2818_R9_0_I2 /\ w1aAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,w1aAction,w1a,Inv10269_2818_R9_0_I2,\prec,\prec
  \* (Inv10269_2818_R9_0_I2,w1bAction)
  <1>11. TypeOK /\ Inv14061_f302_R7_0_I3 /\ Inv10269_2818_R9_0_I2 /\ w1bAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,Inv14061_f302_R7_0_I3,w1bAction,w1b,Inv10269_2818_R9_0_I2,\prec,\prec
  \* (Inv10269_2818_R9_0_I2,w2Action)
  <1>12. TypeOK /\ Inv10269_2818_R9_0_I2 /\ w2Action => Inv10269_2818_R9_0_I2' BY DEF TypeOK,w2Action,w2,Inv10269_2818_R9_0_I2,\prec,\prec
  \* (Inv10269_2818_R9_0_I2,csAction)
  <1>13. TypeOK /\ Inv10269_2818_R9_0_I2 /\ csAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,csAction,cs,Inv10269_2818_R9_0_I2,\prec
  \* (Inv10269_2818_R9_0_I2,exitAction)
  <1>14. TypeOK /\ Inv10269_2818_R9_0_I2 /\ exitAction => Inv10269_2818_R9_0_I2' BY DEF TypeOK,exitAction,exit,Inv10269_2818_R9_0_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2205_3e9d_R12_0_I3
THEOREM L_18 == TypeOK /\ Inv1_b58a_R13_0_I1 /\ Inv2205_3e9d_R12_0_I3 /\ Next => Inv2205_3e9d_R12_0_I3'
  <1>. USE A0
  \* (Inv2205_3e9d_R12_0_I3,ncsAction)
  <1>1. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ ncsAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,ncsAction,ncs,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,e1aAction)
  <1>2. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e1aAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e1aAction,e1a,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,e1bAction)
  <1>3. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e1bAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e1bAction,e1b,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,e2aAction)
  <1>4. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e2aAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e2aAction,e2a,Inv2205_3e9d_R12_0_I3,\prec,Procs
  \* (Inv2205_3e9d_R12_0_I3,e2bAction)
  <1>5. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e2bAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e2bAction,e2b,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,e3aAction)
  <1>6. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e3aAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e3aAction,e3a,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,e3bAction)
  <1>7. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e3bAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e3bAction,e3b,Inv2205_3e9d_R12_0_I3,\prec,\prec
  \* (Inv2205_3e9d_R12_0_I3,e4aAction)
  <1>8. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e4aAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e4aAction,e4a,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,e4bAction)
  <1>9. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ e4bAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,e4bAction,e4b,Inv2205_3e9d_R12_0_I3,\prec,\prec
  \* (Inv2205_3e9d_R12_0_I3,w1aAction)
  <1>10. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ w1aAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,w1aAction,w1a,Inv2205_3e9d_R12_0_I3,\prec,\prec
  \* (Inv2205_3e9d_R12_0_I3,w1bAction)
  <1>11. TypeOK /\ Inv1_b58a_R13_0_I1 /\ Inv2205_3e9d_R12_0_I3 /\ w1bAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,Inv1_b58a_R13_0_I1,w1bAction,w1b,Inv2205_3e9d_R12_0_I3,\prec,\prec
  \* (Inv2205_3e9d_R12_0_I3,w2Action)
  <1>12. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ w2Action => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,w2Action,w2,Inv2205_3e9d_R12_0_I3,\prec,\prec
  \* (Inv2205_3e9d_R12_0_I3,csAction)
  <1>13. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ csAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,csAction,cs,Inv2205_3e9d_R12_0_I3,\prec
  \* (Inv2205_3e9d_R12_0_I3,exitAction)
  <1>14. TypeOK /\ Inv2205_3e9d_R12_0_I3 /\ exitAction => Inv2205_3e9d_R12_0_I3' BY DEF TypeOK,exitAction,exit,Inv2205_3e9d_R12_0_I3,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv12452_548a_R1_1_I2
THEOREM L_19 == TypeOK /\ Inv3155_48f3_R1_0_I2 /\ Inv21465_bb1b_R1_1_I2 /\ Inv19891_1bc3_R1_1_I2 /\ Inv4559_3f08_R1_1_I2 /\ Inv12452_548a_R1_1_I2 /\ Next => Inv12452_548a_R1_1_I2'
  <1>. USE A0
  \* (Inv12452_548a_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv12452_548a_R1_1_I2 /\ ncsAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e1aAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e1bAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e2aAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv12452_548a_R1_1_I2,\prec,Procs
  \* (Inv12452_548a_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e2bAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e3aAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e3bAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv12452_548a_R1_1_I2,\prec,\prec
  \* (Inv12452_548a_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e4aAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv12452_548a_R1_1_I2 /\ e4bAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv12452_548a_R1_1_I2,\prec,\prec
  \* (Inv12452_548a_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv12452_548a_R1_1_I2 /\ w1aAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,Inv12452_548a_R1_1_I2,\prec,\prec
  \* (Inv12452_548a_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv3155_48f3_R1_0_I2 /\ Inv12452_548a_R1_1_I2 /\ w1bAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,Inv3155_48f3_R1_0_I2,w1bAction,w1b,Inv12452_548a_R1_1_I2,\prec,\prec
  \* (Inv12452_548a_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv21465_bb1b_R1_1_I2 /\ Inv19891_1bc3_R1_1_I2 /\ Inv4559_3f08_R1_1_I2 /\ Inv12452_548a_R1_1_I2 /\ w2Action => Inv12452_548a_R1_1_I2' BY DEF TypeOK,Inv21465_bb1b_R1_1_I2,Inv19891_1bc3_R1_1_I2,Inv4559_3f08_R1_1_I2,w2Action,w2,Inv12452_548a_R1_1_I2,\prec,\prec
  \* (Inv12452_548a_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv12452_548a_R1_1_I2 /\ csAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv12452_548a_R1_1_I2,\prec
  \* (Inv12452_548a_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv12452_548a_R1_1_I2 /\ exitAction => Inv12452_548a_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv12452_548a_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv4559_3f08_R1_1_I2
THEOREM L_20 == TypeOK /\ Inv26_b6ff_R2_0_I3 /\ Inv4559_3f08_R1_1_I2 /\ Next => Inv4559_3f08_R1_1_I2'
  <1>. USE A0
  \* (Inv4559_3f08_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ ncsAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,ncsAction,ncs,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,e1aAction)
  <1>2. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e1aAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e1aAction,e1a,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,e1bAction)
  <1>3. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e1bAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e1bAction,e1b,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,e2aAction)
  <1>4. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e2aAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e2aAction,e2a,Inv4559_3f08_R1_1_I2,\prec,Procs
  \* (Inv4559_3f08_R1_1_I2,e2bAction)
  <1>5. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e2bAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e2bAction,e2b,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,e3aAction)
  <1>6. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e3aAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e3aAction,e3a,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,e3bAction)
  <1>7. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e3bAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e3bAction,e3b,Inv4559_3f08_R1_1_I2,\prec,\prec
  \* (Inv4559_3f08_R1_1_I2,e4aAction)
  <1>8. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e4aAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e4aAction,e4a,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,e4bAction)
  <1>9. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ e4bAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,e4bAction,e4b,Inv4559_3f08_R1_1_I2,\prec,\prec
  \* (Inv4559_3f08_R1_1_I2,w1aAction)
  <1>10. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ w1aAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,w1aAction,w1a,Inv4559_3f08_R1_1_I2,\prec,\prec
  \* (Inv4559_3f08_R1_1_I2,w1bAction)
  <1>11. TypeOK /\ Inv26_b6ff_R2_0_I3 /\ Inv4559_3f08_R1_1_I2 /\ w1bAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,Inv26_b6ff_R2_0_I3,w1bAction,w1b,Inv4559_3f08_R1_1_I2,\prec,\prec
  \* (Inv4559_3f08_R1_1_I2,w2Action)
  <1>12. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ w2Action => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,w2Action,w2,Inv4559_3f08_R1_1_I2,\prec,\prec
  \* (Inv4559_3f08_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ csAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,csAction,cs,Inv4559_3f08_R1_1_I2,\prec
  \* (Inv4559_3f08_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv4559_3f08_R1_1_I2 /\ exitAction => Inv4559_3f08_R1_1_I2' BY DEF TypeOK,exitAction,exit,Inv4559_3f08_R1_1_I2,\prec
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0
 DEF \prec, ProcSet
    <1>0. Init => TypeOK 
      <2> SUFFICES ASSUME Init
                   PROVE  TypeOK
        OBVIOUS
      <2>1. num \in [Procs -> Nat]
        BY DEF Init, TypeOK, IndGlobal
      <2>2. flag \in [Procs -> BOOLEAN]
        BY DEF Init, TypeOK, IndGlobal
      <2>3. unchecked \in [Procs -> SUBSET Procs]
        BY DEF Init, TypeOK, IndGlobal
      <2>4. max \in [Procs -> Nat]
        BY DEF Init, TypeOK, IndGlobal
      <2>5. nxt \in [Procs -> Procs]
        BY DEF Init, TypeOK, IndGlobal
      <2>6. pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]
        BY DEF Init, TypeOK, IndGlobal
      <2>7. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_MutualExclusion
    <1>2. Init => Inv23439_af2b_R0_0_I2 BY DEF Init, Inv23439_af2b_R0_0_I2, IndGlobal
    <1>3. Init => Inv3155_48f3_R1_0_I2 BY DEF Init, Inv3155_48f3_R1_0_I2, IndGlobal
    <1>4. Init => Inv6938_a43e_R2_0_I3 BY DEF Init, Inv6938_a43e_R2_0_I3, IndGlobal
    <1>5. Init => Inv14061_f302_R7_0_I3 BY DEF Init, Inv14061_f302_R7_0_I3, IndGlobal
    <1>6. Init => Inv0_b3ba_R10_0_I0 BY DEF Init, Inv0_b3ba_R10_0_I0, IndGlobal
    <1>7. Init => Inv1_b58a_R13_0_I1 BY DEF Init, Inv1_b58a_R13_0_I1, IndGlobal
    <1>8. Init => Inv738_26ef_R13_1_I2 BY DEF Init, Inv738_26ef_R13_1_I2, IndGlobal
    <1>9. Init => Inv48_180c_R17_0_I1 BY DEF Init, Inv48_180c_R17_0_I1, IndGlobal
    <1>10. Init => Inv5493_34f2_R10_1_I2 BY DEF Init, Inv5493_34f2_R10_1_I2, IndGlobal
    <1>11. Init => Inv296_b692_R14_1_I1 BY DEF Init, Inv296_b692_R14_1_I1, IndGlobal
    <1>12. Init => Inv11_73d9_R7_1_I1 BY DEF Init, Inv11_73d9_R7_1_I1, IndGlobal
    <1>13. Init => Inv26_b6ff_R2_0_I3 BY DEF Init, Inv26_b6ff_R2_0_I3, IndGlobal
    <1>14. Init => Inv21465_bb1b_R1_1_I2 BY DEF Init, Inv21465_bb1b_R1_1_I2, IndGlobal
    <1>15. Init => Inv19891_1bc3_R1_1_I2 BY DEF Init, Inv19891_1bc3_R1_1_I2, IndGlobal
    <1>16. Init => Inv1222_288c_R4_0_I2 BY DEF Init, Inv1222_288c_R4_0_I2, IndGlobal
    <1>17. Init => Inv10269_2818_R9_0_I2 BY DEF Init, Inv10269_2818_R9_0_I2, IndGlobal
    <1>18. Init => Inv2205_3e9d_R12_0_I3 BY DEF Init, Inv2205_3e9d_R12_0_I3, IndGlobal
    <1>19. Init => Inv12452_548a_R1_1_I2 BY DEF Init, Inv12452_548a_R1_1_I2, IndGlobal
    <1>20. Init => Inv4559_3f08_R1_1_I2 BY DEF Init, Inv4559_3f08_R1_1_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20 DEF Next, IndGlobal












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
\* Last modified Sat Sep 14 14:19:51 EDT 2024 by willyschultz
\* Last modified Tue Dec 18 13:48:46 PST 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
