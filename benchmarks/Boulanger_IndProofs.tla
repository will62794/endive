------------------------------- MODULE Boulanger_IndProofs -------------------------------
EXTENDS Boulanger


\* Proof Graph Stats
\* ==================
\* num proof graph nodes: 10
\* num proof obligations: 140
Safety == H_MutualExclusion
Inv7190_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(pc[VARI] = "cs") \/ (~(unchecked[VARJ] = {})) \/ (~(pc[VARJ] = "w1"))
Inv2239_R0_1_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "cs"))
Inv1976_R0_1_I1 == \A VARI \in Procs : (previous[VARI] = -1) \/ (~(nxt[VARI] = VARI))
Inv44_R0_1_I1 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
Inv3027_R0_1_I1 == \A VARI \in Procs : ~(pc[VARI] = "w2") \/ (~(unchecked[VARI] = {}))
Inv2245_R0_1_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "ncs"))
Inv6256_R1_1_I2 == \A VARI \in Procs : (unchecked[VARI] = 1..(VARI-1)) \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARI] = "w1"))
Inv1783_R3_0_I1 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(pc[VARI] = "w2"))
Inv466_R6_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "exit"))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv7190_R0_0_I2
  /\ Inv2239_R0_1_I1
  /\ Inv44_R0_1_I1
  /\ Inv6256_R1_1_I2
  /\ Inv3027_R0_1_I1
  /\ Inv1976_R0_1_I1
  /\ Inv1783_R3_0_I1
  /\ Inv2245_R0_1_I1
  /\ Inv466_R6_0_I1


\* mean in-degree: 0.9
\* median in-degree: 0
\* max in-degree: 4
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,ncsAction)
  <1>1. TypeOK /\ TypeOK /\ ncsAction => TypeOK'
       BY DEF TypeOK,ncsAction,ncs,TypeOK
  \* (TypeOK,e1Action)
  <1>2. TypeOK /\ TypeOK /\ e1Action => TypeOK'
       BY DEF TypeOK,e1Action,e1,TypeOK
  \* (TypeOK,e1MaxUpdateAction)
  <1>3. TypeOK /\ TypeOK /\ e1MaxUpdateAction => TypeOK'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,TypeOK
  \* (TypeOK,e2Action)
  <1>4. TypeOK /\ TypeOK /\ e2Action => TypeOK'
       BY DEF TypeOK,e2Action,e2,TypeOK
  \* (TypeOK,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ TypeOK /\ e2UncheckedEmptyAction => TypeOK'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,TypeOK
  \* (TypeOK,e3Action)
  <1>6. TypeOK /\ TypeOK /\ e3Action => TypeOK'
       BY DEF TypeOK,e3Action,e3,TypeOK
  \* (TypeOK,e3MaxAction)
  <1>7. TypeOK /\ TypeOK /\ e3MaxAction => TypeOK'
       BY DEF TypeOK,e3MaxAction,e3Max,TypeOK
  \* (TypeOK,e4Action)
  <1>8. TypeOK /\ TypeOK /\ e4Action => TypeOK'
       BY DEF TypeOK,e4Action,e4,TypeOK
  \* (TypeOK,w1Action)
  <1>9. TypeOK /\ TypeOK /\ w1Action => TypeOK'
       BY DEF TypeOK,w1Action,w1,TypeOK
  \* (TypeOK,w1NegAction)
  <1>10. TypeOK /\ TypeOK /\ w1NegAction => TypeOK'
       BY DEF TypeOK,w1NegAction,w1Neg,TypeOK
  \* (TypeOK,w2Action)
  <1>11. TypeOK /\ TypeOK /\ w2Action => TypeOK'
       BY DEF TypeOK,w2Action,w2,TypeOK
  \* (TypeOK,w2PrevAction)
  <1>12. TypeOK /\ TypeOK /\ w2PrevAction => TypeOK'
       BY DEF TypeOK,w2PrevAction,w2Prev,TypeOK
  \* (TypeOK,csAction)
  <1>13. TypeOK /\ TypeOK /\ csAction => TypeOK'
       BY DEF TypeOK,csAction,cs,TypeOK
  \* (TypeOK,exitAction)
  <1>14. TypeOK /\ TypeOK /\ exitAction => TypeOK'
       BY DEF TypeOK,exitAction,exit,TypeOK
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\* (ROOT SAFETY PROP)
ASSUME A1 == Nats \subseteq Nat /\ N \in Nat
\*** Safety
THEOREM L_1 == TypeOK /\ Inv7190_R0_0_I2 /\ Inv1976_R0_1_I1 /\ Inv2245_R0_1_I1 /\ Safety /\ Next => Safety'
  \* (Safety,ncsAction)
  <1>1. TypeOK /\ Safety /\ ncsAction => Safety'
       BY DEF TypeOK,ncsAction,ncs,Safety,H_MutualExclusion
  \* (Safety,e1Action)
  <1>2. TypeOK /\ Safety /\ e1Action => Safety'
       BY DEF TypeOK,e1Action,e1,Safety,H_MutualExclusion
  \* (Safety,e1MaxUpdateAction)
  <1>3. TypeOK /\ Safety /\ e1MaxUpdateAction => Safety'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Safety,H_MutualExclusion
  \* (Safety,e2Action)
  <1>4. TypeOK /\ Safety /\ e2Action => Safety'
       BY DEF TypeOK,e2Action,e2,Safety,H_MutualExclusion
  \* (Safety,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Safety /\ e2UncheckedEmptyAction => Safety'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Safety,H_MutualExclusion
  \* (Safety,e3Action)
  <1>6. TypeOK /\ Safety /\ e3Action => Safety'
       BY DEF TypeOK,e3Action,e3,Safety,H_MutualExclusion
  \* (Safety,e3MaxAction)
  <1>7. TypeOK /\ Safety /\ e3MaxAction => Safety'
       BY DEF TypeOK,e3MaxAction,e3Max,Safety,H_MutualExclusion
  \* (Safety,e4Action)
  <1>8. TypeOK /\ Safety /\ e4Action => Safety'
       BY DEF TypeOK,e4Action,e4,Safety,H_MutualExclusion
  \* (Safety,w1Action)
  <1>9. TypeOK /\ Safety /\ w1Action => Safety'
       BY DEF TypeOK,w1Action,w1,Safety,H_MutualExclusion
  \* (Safety,w1NegAction)
  <1>10. TypeOK /\ Inv7190_R0_0_I2 /\ Safety /\ w1NegAction => Safety'
       BY DEF TypeOK,Inv7190_R0_0_I2,w1NegAction,w1Neg,Safety,H_MutualExclusion
  \* (Safety,w2Action)
  <1>11. TypeOK /\ Inv1976_R0_1_I1 /\ Inv2245_R0_1_I1 /\ Safety /\ w2Action => Safety'
       BY A1 DEF TypeOK,Inv1976_R0_1_I1,Inv2245_R0_1_I1,w2Action,w2,Safety,H_MutualExclusion,Procs,w2Cond,\prec
  \* (Safety,w2PrevAction)
  <1>12. TypeOK /\ Safety /\ w2PrevAction => Safety'
       BY DEF TypeOK,w2PrevAction,w2Prev,Safety,H_MutualExclusion
  \* (Safety,csAction)
  <1>13. TypeOK /\ Safety /\ csAction => Safety'
       BY DEF TypeOK,csAction,cs,Safety,H_MutualExclusion
  \* (Safety,exitAction)
  <1>14. TypeOK /\ Safety /\ exitAction => Safety'
       BY DEF TypeOK,exitAction,exit,Safety,H_MutualExclusion
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv7190_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv2239_R0_1_I1 /\ Inv44_R0_1_I1 /\ Inv6256_R1_1_I2 /\ Inv3027_R0_1_I1 /\ Inv7190_R0_0_I2 /\ Next => Inv7190_R0_0_I2'
  \* (Inv7190_R0_0_I2,ncsAction)
  <1>1. TypeOK /\ Inv7190_R0_0_I2 /\ ncsAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e1Action)
  <1>2. TypeOK /\ Inv7190_R0_0_I2 /\ e1Action => Inv7190_R0_0_I2'
       BY DEF TypeOK,e1Action,e1,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv7190_R0_0_I2 /\ e1MaxUpdateAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e2Action)
  <1>4. TypeOK /\ Inv7190_R0_0_I2 /\ e2Action => Inv7190_R0_0_I2'
       BY DEF TypeOK,e2Action,e2,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv7190_R0_0_I2 /\ e2UncheckedEmptyAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e3Action)
  <1>6. TypeOK /\ Inv7190_R0_0_I2 /\ e3Action => Inv7190_R0_0_I2'
       BY DEF TypeOK,e3Action,e3,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e3MaxAction)
  <1>7. TypeOK /\ Inv7190_R0_0_I2 /\ e3MaxAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,e4Action)
  <1>8. TypeOK /\ Inv2239_R0_1_I1 /\ Inv44_R0_1_I1 /\ Inv7190_R0_0_I2 /\ e4Action => Inv7190_R0_0_I2'
       BY DEF TypeOK,Inv2239_R0_1_I1,Inv44_R0_1_I1,e4Action,e4,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,w1Action)
  <1>9. TypeOK /\ Inv7190_R0_0_I2 /\ w1Action => Inv7190_R0_0_I2'
       BY DEF TypeOK,w1Action,w1,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,w1NegAction)
  <1>10. TypeOK /\ Inv6256_R1_1_I2 /\ Inv7190_R0_0_I2 /\ w1NegAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,Inv6256_R1_1_I2,w1NegAction,w1Neg,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,w2Action)
  <1>11. TypeOK /\ Inv3027_R0_1_I1 /\ Inv7190_R0_0_I2 /\ w2Action => Inv7190_R0_0_I2'
       BY DEF TypeOK,Inv3027_R0_1_I1,w2Action,w2,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,w2PrevAction)
  <1>12. TypeOK /\ Inv7190_R0_0_I2 /\ w2PrevAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,csAction)
  <1>13. TypeOK /\ Inv7190_R0_0_I2 /\ csAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,csAction,cs,Inv7190_R0_0_I2
  \* (Inv7190_R0_0_I2,exitAction)
  <1>14. TypeOK /\ Inv7190_R0_0_I2 /\ exitAction => Inv7190_R0_0_I2'
       BY DEF TypeOK,exitAction,exit,Inv7190_R0_0_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2239_R0_1_I1
THEOREM L_3 == TypeOK /\ Inv2239_R0_1_I1 /\ Next => Inv2239_R0_1_I1'
  \* (Inv2239_R0_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv2239_R0_1_I1 /\ ncsAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e1Action)
  <1>2. TypeOK /\ Inv2239_R0_1_I1 /\ e1Action => Inv2239_R0_1_I1'
       BY DEF TypeOK,e1Action,e1,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv2239_R0_1_I1 /\ e1MaxUpdateAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e2Action)
  <1>4. TypeOK /\ Inv2239_R0_1_I1 /\ e2Action => Inv2239_R0_1_I1'
       BY DEF TypeOK,e2Action,e2,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv2239_R0_1_I1 /\ e2UncheckedEmptyAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e3Action)
  <1>6. TypeOK /\ Inv2239_R0_1_I1 /\ e3Action => Inv2239_R0_1_I1'
       BY DEF TypeOK,e3Action,e3,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv2239_R0_1_I1 /\ e3MaxAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,e4Action)
  <1>8. TypeOK /\ Inv2239_R0_1_I1 /\ e4Action => Inv2239_R0_1_I1'
       BY DEF TypeOK,e4Action,e4,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,w1Action)
  <1>9. TypeOK /\ Inv2239_R0_1_I1 /\ w1Action => Inv2239_R0_1_I1'
       BY DEF TypeOK,w1Action,w1,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,w1NegAction)
  <1>10. TypeOK /\ Inv2239_R0_1_I1 /\ w1NegAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,w2Action)
  <1>11. TypeOK /\ Inv2239_R0_1_I1 /\ w2Action => Inv2239_R0_1_I1'
       BY DEF TypeOK,w2Action,w2,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv2239_R0_1_I1 /\ w2PrevAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,csAction)
  <1>13. TypeOK /\ Inv2239_R0_1_I1 /\ csAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,csAction,cs,Inv2239_R0_1_I1
  \* (Inv2239_R0_1_I1,exitAction)
  <1>14. TypeOK /\ Inv2239_R0_1_I1 /\ exitAction => Inv2239_R0_1_I1'
       BY DEF TypeOK,exitAction,exit,Inv2239_R0_1_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv44_R0_1_I1
THEOREM L_4 == TypeOK /\ Inv44_R0_1_I1 /\ Next => Inv44_R0_1_I1'
  \* (Inv44_R0_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv44_R0_1_I1 /\ ncsAction => Inv44_R0_1_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e1Action)
  <1>2. TypeOK /\ Inv44_R0_1_I1 /\ e1Action => Inv44_R0_1_I1'
       BY DEF TypeOK,e1Action,e1,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv44_R0_1_I1 /\ e1MaxUpdateAction => Inv44_R0_1_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e2Action)
  <1>4. TypeOK /\ Inv44_R0_1_I1 /\ e2Action => Inv44_R0_1_I1'
       BY DEF TypeOK,e2Action,e2,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv44_R0_1_I1 /\ e2UncheckedEmptyAction => Inv44_R0_1_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e3Action)
  <1>6. TypeOK /\ Inv44_R0_1_I1 /\ e3Action => Inv44_R0_1_I1'
       BY DEF TypeOK,e3Action,e3,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv44_R0_1_I1 /\ e3MaxAction => Inv44_R0_1_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,e4Action)
  <1>8. TypeOK /\ Inv44_R0_1_I1 /\ e4Action => Inv44_R0_1_I1'
       BY DEF TypeOK,e4Action,e4,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,w1Action)
  <1>9. TypeOK /\ Inv44_R0_1_I1 /\ w1Action => Inv44_R0_1_I1'
       BY DEF TypeOK,w1Action,w1,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,w1NegAction)
  <1>10. TypeOK /\ Inv44_R0_1_I1 /\ w1NegAction => Inv44_R0_1_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,w2Action)
  <1>11. TypeOK /\ Inv44_R0_1_I1 /\ w2Action => Inv44_R0_1_I1'
       BY DEF TypeOK,w2Action,w2,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv44_R0_1_I1 /\ w2PrevAction => Inv44_R0_1_I1'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,csAction)
  <1>13. TypeOK /\ Inv44_R0_1_I1 /\ csAction => Inv44_R0_1_I1'
       BY DEF TypeOK,csAction,cs,Inv44_R0_1_I1
  \* (Inv44_R0_1_I1,exitAction)
  <1>14. TypeOK /\ Inv44_R0_1_I1 /\ exitAction => Inv44_R0_1_I1'
       BY DEF TypeOK,exitAction,exit,Inv44_R0_1_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv6256_R1_1_I2
THEOREM L_5 == TypeOK /\ Inv6256_R1_1_I2 /\ Next => Inv6256_R1_1_I2'
  \* (Inv6256_R1_1_I2,ncsAction)
  <1>1. TypeOK /\ Inv6256_R1_1_I2 /\ ncsAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,ncsAction,ncs,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e1Action)
  <1>2. TypeOK /\ Inv6256_R1_1_I2 /\ e1Action => Inv6256_R1_1_I2'
       BY DEF TypeOK,e1Action,e1,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv6256_R1_1_I2 /\ e1MaxUpdateAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e2Action)
  <1>4. TypeOK /\ Inv6256_R1_1_I2 /\ e2Action => Inv6256_R1_1_I2'
       BY DEF TypeOK,e2Action,e2,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv6256_R1_1_I2 /\ e2UncheckedEmptyAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e3Action)
  <1>6. TypeOK /\ Inv6256_R1_1_I2 /\ e3Action => Inv6256_R1_1_I2'
       BY DEF TypeOK,e3Action,e3,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e3MaxAction)
  <1>7. TypeOK /\ Inv6256_R1_1_I2 /\ e3MaxAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,e4Action)
  <1>8. TypeOK /\ Inv6256_R1_1_I2 /\ e4Action => Inv6256_R1_1_I2'
       BY DEF TypeOK,e4Action,e4,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,w1Action)
  <1>9. TypeOK /\ Inv6256_R1_1_I2 /\ w1Action => Inv6256_R1_1_I2'
       BY DEF TypeOK,w1Action,w1,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,w1NegAction)
  <1>10. TypeOK /\ Inv6256_R1_1_I2 /\ w1NegAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,w2Action)
  <1>11. TypeOK /\ Inv6256_R1_1_I2 /\ w2Action => Inv6256_R1_1_I2'
       BY DEF TypeOK,w2Action,w2,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,w2PrevAction)
  <1>12. TypeOK /\ Inv6256_R1_1_I2 /\ w2PrevAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,csAction)
  <1>13. TypeOK /\ Inv6256_R1_1_I2 /\ csAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,csAction,cs,Inv6256_R1_1_I2
  \* (Inv6256_R1_1_I2,exitAction)
  <1>14. TypeOK /\ Inv6256_R1_1_I2 /\ exitAction => Inv6256_R1_1_I2'
       BY DEF TypeOK,exitAction,exit,Inv6256_R1_1_I2
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv3027_R0_1_I1
THEOREM L_6 == TypeOK /\ Inv3027_R0_1_I1 /\ Next => Inv3027_R0_1_I1'
  \* (Inv3027_R0_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv3027_R0_1_I1 /\ ncsAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e1Action)
  <1>2. TypeOK /\ Inv3027_R0_1_I1 /\ e1Action => Inv3027_R0_1_I1'
       BY DEF TypeOK,e1Action,e1,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv3027_R0_1_I1 /\ e1MaxUpdateAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e2Action)
  <1>4. TypeOK /\ Inv3027_R0_1_I1 /\ e2Action => Inv3027_R0_1_I1'
       BY DEF TypeOK,e2Action,e2,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv3027_R0_1_I1 /\ e2UncheckedEmptyAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e3Action)
  <1>6. TypeOK /\ Inv3027_R0_1_I1 /\ e3Action => Inv3027_R0_1_I1'
       BY DEF TypeOK,e3Action,e3,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv3027_R0_1_I1 /\ e3MaxAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,e4Action)
  <1>8. TypeOK /\ Inv3027_R0_1_I1 /\ e4Action => Inv3027_R0_1_I1'
       BY DEF TypeOK,e4Action,e4,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,w1Action)
  <1>9. TypeOK /\ Inv3027_R0_1_I1 /\ w1Action => Inv3027_R0_1_I1'
       BY DEF TypeOK,w1Action,w1,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,w1NegAction)
  <1>10. TypeOK /\ Inv3027_R0_1_I1 /\ w1NegAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,w2Action)
  <1>11. TypeOK /\ Inv3027_R0_1_I1 /\ w2Action => Inv3027_R0_1_I1'
       BY DEF TypeOK,w2Action,w2,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv3027_R0_1_I1 /\ w2PrevAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,csAction)
  <1>13. TypeOK /\ Inv3027_R0_1_I1 /\ csAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,csAction,cs,Inv3027_R0_1_I1
  \* (Inv3027_R0_1_I1,exitAction)
  <1>14. TypeOK /\ Inv3027_R0_1_I1 /\ exitAction => Inv3027_R0_1_I1'
       BY DEF TypeOK,exitAction,exit,Inv3027_R0_1_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1976_R0_1_I1
THEOREM L_7 == TypeOK /\ Inv1783_R3_0_I1 /\ Inv1976_R0_1_I1 /\ Next => Inv1976_R0_1_I1'
  \* (Inv1976_R0_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv1976_R0_1_I1 /\ ncsAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e1Action)
  <1>2. TypeOK /\ Inv1976_R0_1_I1 /\ e1Action => Inv1976_R0_1_I1'
       BY DEF TypeOK,e1Action,e1,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv1976_R0_1_I1 /\ e1MaxUpdateAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e2Action)
  <1>4. TypeOK /\ Inv1976_R0_1_I1 /\ e2Action => Inv1976_R0_1_I1'
       BY DEF TypeOK,e2Action,e2,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv1976_R0_1_I1 /\ e2UncheckedEmptyAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e3Action)
  <1>6. TypeOK /\ Inv1976_R0_1_I1 /\ e3Action => Inv1976_R0_1_I1'
       BY DEF TypeOK,e3Action,e3,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv1976_R0_1_I1 /\ e3MaxAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,e4Action)
  <1>8. TypeOK /\ Inv1976_R0_1_I1 /\ e4Action => Inv1976_R0_1_I1'
       BY DEF TypeOK,e4Action,e4,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,w1Action)
  <1>9. TypeOK /\ Inv1976_R0_1_I1 /\ w1Action => Inv1976_R0_1_I1'
       BY DEF TypeOK,w1Action,w1,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,w1NegAction)
  <1>10. TypeOK /\ Inv1976_R0_1_I1 /\ w1NegAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,w2Action)
  <1>11. TypeOK /\ Inv1976_R0_1_I1 /\ w2Action => Inv1976_R0_1_I1'
       BY DEF TypeOK,w2Action,w2,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv1783_R3_0_I1 /\ Inv1976_R0_1_I1 /\ w2PrevAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,Inv1783_R3_0_I1,w2PrevAction,w2Prev,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,csAction)
  <1>13. TypeOK /\ Inv1976_R0_1_I1 /\ csAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,csAction,cs,Inv1976_R0_1_I1
  \* (Inv1976_R0_1_I1,exitAction)
  <1>14. TypeOK /\ Inv1976_R0_1_I1 /\ exitAction => Inv1976_R0_1_I1'
       BY DEF TypeOK,exitAction,exit,Inv1976_R0_1_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv1783_R3_0_I1
THEOREM L_8 == TypeOK /\ Inv1783_R3_0_I1 /\ Next => Inv1783_R3_0_I1'
  \* (Inv1783_R3_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1783_R3_0_I1 /\ ncsAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1783_R3_0_I1 /\ e1Action => Inv1783_R3_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv1783_R3_0_I1 /\ e1MaxUpdateAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e2Action)
  <1>4. TypeOK /\ Inv1783_R3_0_I1 /\ e2Action => Inv1783_R3_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv1783_R3_0_I1 /\ e2UncheckedEmptyAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e3Action)
  <1>6. TypeOK /\ Inv1783_R3_0_I1 /\ e3Action => Inv1783_R3_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv1783_R3_0_I1 /\ e3MaxAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,e4Action)
  <1>8. TypeOK /\ Inv1783_R3_0_I1 /\ e4Action => Inv1783_R3_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,w1Action)
  <1>9. TypeOK /\ Inv1783_R3_0_I1 /\ w1Action => Inv1783_R3_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,w1NegAction)
  <1>10. TypeOK /\ Inv1783_R3_0_I1 /\ w1NegAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,w2Action)
  <1>11. TypeOK /\ Inv1783_R3_0_I1 /\ w2Action => Inv1783_R3_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv1783_R3_0_I1 /\ w2PrevAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,csAction)
  <1>13. TypeOK /\ Inv1783_R3_0_I1 /\ csAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1783_R3_0_I1
  \* (Inv1783_R3_0_I1,exitAction)
  <1>14. TypeOK /\ Inv1783_R3_0_I1 /\ exitAction => Inv1783_R3_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1783_R3_0_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv2245_R0_1_I1
THEOREM L_9 == TypeOK /\ Inv466_R6_0_I1 /\ Inv2245_R0_1_I1 /\ Next => Inv2245_R0_1_I1'
  \* (Inv2245_R0_1_I1,ncsAction)
  <1>1. TypeOK /\ Inv2245_R0_1_I1 /\ ncsAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e1Action)
  <1>2. TypeOK /\ Inv2245_R0_1_I1 /\ e1Action => Inv2245_R0_1_I1'
       BY DEF TypeOK,e1Action,e1,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv2245_R0_1_I1 /\ e1MaxUpdateAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e2Action)
  <1>4. TypeOK /\ Inv2245_R0_1_I1 /\ e2Action => Inv2245_R0_1_I1'
       BY DEF TypeOK,e2Action,e2,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv2245_R0_1_I1 /\ e2UncheckedEmptyAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e3Action)
  <1>6. TypeOK /\ Inv2245_R0_1_I1 /\ e3Action => Inv2245_R0_1_I1'
       BY DEF TypeOK,e3Action,e3,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv2245_R0_1_I1 /\ e3MaxAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,e4Action)
  <1>8. TypeOK /\ Inv2245_R0_1_I1 /\ e4Action => Inv2245_R0_1_I1'
       BY DEF TypeOK,e4Action,e4,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,w1Action)
  <1>9. TypeOK /\ Inv2245_R0_1_I1 /\ w1Action => Inv2245_R0_1_I1'
       BY DEF TypeOK,w1Action,w1,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,w1NegAction)
  <1>10. TypeOK /\ Inv2245_R0_1_I1 /\ w1NegAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,w2Action)
  <1>11. TypeOK /\ Inv2245_R0_1_I1 /\ w2Action => Inv2245_R0_1_I1'
       BY DEF TypeOK,w2Action,w2,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv2245_R0_1_I1 /\ w2PrevAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,csAction)
  <1>13. TypeOK /\ Inv2245_R0_1_I1 /\ csAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,csAction,cs,Inv2245_R0_1_I1
  \* (Inv2245_R0_1_I1,exitAction)
  <1>14. TypeOK /\ Inv466_R6_0_I1 /\ Inv2245_R0_1_I1 /\ exitAction => Inv2245_R0_1_I1'
       BY DEF TypeOK,Inv466_R6_0_I1,exitAction,exit,Inv2245_R0_1_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


\*** Inv466_R6_0_I1
THEOREM L_10 == TypeOK /\ Inv466_R6_0_I1 /\ Next => Inv466_R6_0_I1'
  \* (Inv466_R6_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv466_R6_0_I1 /\ ncsAction => Inv466_R6_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e1Action)
  <1>2. TypeOK /\ Inv466_R6_0_I1 /\ e1Action => Inv466_R6_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e1MaxUpdateAction)
  <1>3. TypeOK /\ Inv466_R6_0_I1 /\ e1MaxUpdateAction => Inv466_R6_0_I1'
       BY DEF TypeOK,e1MaxUpdateAction,e1MaxUpdate,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e2Action)
  <1>4. TypeOK /\ Inv466_R6_0_I1 /\ e2Action => Inv466_R6_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e2UncheckedEmptyAction)
  <1>5. TypeOK /\ Inv466_R6_0_I1 /\ e2UncheckedEmptyAction => Inv466_R6_0_I1'
       BY DEF TypeOK,e2UncheckedEmptyAction,e2UncheckedEmpty,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e3Action)
  <1>6. TypeOK /\ Inv466_R6_0_I1 /\ e3Action => Inv466_R6_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e3MaxAction)
  <1>7. TypeOK /\ Inv466_R6_0_I1 /\ e3MaxAction => Inv466_R6_0_I1'
       BY DEF TypeOK,e3MaxAction,e3Max,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,e4Action)
  <1>8. TypeOK /\ Inv466_R6_0_I1 /\ e4Action => Inv466_R6_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,w1Action)
  <1>9. TypeOK /\ Inv466_R6_0_I1 /\ w1Action => Inv466_R6_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,w1NegAction)
  <1>10. TypeOK /\ Inv466_R6_0_I1 /\ w1NegAction => Inv466_R6_0_I1'
       BY DEF TypeOK,w1NegAction,w1Neg,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,w2Action)
  <1>11. TypeOK /\ Inv466_R6_0_I1 /\ w2Action => Inv466_R6_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,w2PrevAction)
  <1>12. TypeOK /\ Inv466_R6_0_I1 /\ w2PrevAction => Inv466_R6_0_I1'
       BY DEF TypeOK,w2PrevAction,w2Prev,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,csAction)
  <1>13. TypeOK /\ Inv466_R6_0_I1 /\ csAction => Inv466_R6_0_I1'
       BY DEF TypeOK,csAction,cs,Inv466_R6_0_I1
  \* (Inv466_R6_0_I1,exitAction)
  <1>14. TypeOK /\ Inv466_R6_0_I1 /\ exitAction => Inv466_R6_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv466_R6_0_I1
<1>15. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10 DEF Next, IndGlobal




\* Inv21195_R4_0_I3 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARI] = "w1"))
=============================================================================
\* Modification History
\* Last modified Wed Apr 03 02:55:37 EDT 2024 by willyschultz
\* Last modified Tue Dec 18 13:48:46 PST 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
