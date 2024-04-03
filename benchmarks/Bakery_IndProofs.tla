------------------------------- MODULE Bakery_IndProofs -------------------------------
EXTENDS Bakery

\* Proof Graph Stats
\* ==================
\* num proof graph nodes: 12
\* num proof obligations: 108
Safety == H_MutualExclusion
Inv1230_R0_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "cs"))
Inv1470_R0_0_I1 == \A VARI \in Procs : ~(flag[VARI]) \/ (~(pc[VARI] = "cs"))
Inv1477_R0_0_I1 == \A VARI \in Procs : ~(flag[VARI]) \/ (~(pc[VARI] = "w1"))
Inv32_R0_0_I1 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
Inv1578_R0_0_I1 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(pc[VARI] = "w2"))
Inv370_R0_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e2"))
Inv371_R0_0_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e3"))
Inv1231_R0_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "e1"))
Inv1579_R3_0_I1 == \A VARI \in Procs : ~(flag[VARI]) \/ (~(pc[VARI] = "w2"))
Inv521_R8_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "ncs"))
Inv520_R10_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "exit"))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv1230_R0_0_I1
  /\ Inv1470_R0_0_I1
  /\ Inv1477_R0_0_I1
  /\ Inv1579_R3_0_I1
  /\ Inv32_R0_0_I1
  /\ Inv1578_R0_0_I1
  /\ Inv370_R0_0_I1
  /\ Inv371_R0_0_I1
  /\ Inv1231_R0_0_I1
  /\ Inv521_R8_0_I1
  /\ Inv520_R10_0_I1


\* mean in-degree: 1.0
\* median in-degree: 0
\* max in-degree: 8
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
  \* (TypeOK,e2Action)
  <1>3. TypeOK /\ TypeOK /\ e2Action => TypeOK'
       BY DEF TypeOK,e2Action,e2,TypeOK
  \* (TypeOK,e3Action)
  <1>4. TypeOK /\ TypeOK /\ e3Action => TypeOK'
       BY DEF TypeOK,e3Action,e3,TypeOK
  \* (TypeOK,e4Action)
  <1>5. TypeOK /\ TypeOK /\ e4Action => TypeOK'
       BY DEF TypeOK,e4Action,e4,TypeOK
  \* (TypeOK,w1Action)
  <1>6. TypeOK /\ TypeOK /\ w1Action => TypeOK'
       BY DEF TypeOK,w1Action,w1,TypeOK
  \* (TypeOK,w2Action)
  <1>7. TypeOK /\ TypeOK /\ w2Action => TypeOK'
       BY DEF TypeOK,w2Action,w2,TypeOK
  \* (TypeOK,csAction)
  <1>8. TypeOK /\ TypeOK /\ csAction => TypeOK'
       BY DEF TypeOK,csAction,cs,TypeOK
  \* (TypeOK,exitAction)
  <1>9. TypeOK /\ TypeOK /\ exitAction => TypeOK'
       BY DEF TypeOK,exitAction,exit,TypeOK
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv1230_R0_0_I1 /\ Inv1470_R0_0_I1 /\ Inv1477_R0_0_I1 /\ Inv32_R0_0_I1 /\ Inv1578_R0_0_I1 /\ Inv370_R0_0_I1 /\ Inv371_R0_0_I1 /\ Inv1231_R0_0_I1 /\ Safety /\ Next => Safety'
  \* (Safety,ncsAction)
  <1>1. TypeOK /\ Safety /\ ncsAction => Safety'
       BY DEF TypeOK,ncsAction,ncs,Safety,H_MutualExclusion
  \* (Safety,e1Action)
  <1>2. TypeOK /\ Safety /\ e1Action => Safety'
       BY DEF TypeOK,e1Action,e1,Safety,H_MutualExclusion
  \* (Safety,e2Action)
  <1>3. TypeOK /\ Safety /\ e2Action => Safety'
       BY DEF TypeOK,e2Action,e2,Safety,H_MutualExclusion
  \* (Safety,e3Action)
  <1>4. TypeOK /\ Safety /\ e3Action => Safety'
       BY DEF TypeOK,e3Action,e3,Safety,H_MutualExclusion
  \* (Safety,e4Action)
  <1>5. TypeOK /\ Safety /\ e4Action => Safety'
       BY DEF TypeOK,e4Action,e4,Safety,H_MutualExclusion
  \* (Safety,w1Action)
  <1>6. TypeOK /\ Inv1230_R0_0_I1 /\ Inv1470_R0_0_I1 /\ Inv1477_R0_0_I1 /\ Inv32_R0_0_I1 /\ Inv1578_R0_0_I1 /\ Inv370_R0_0_I1 /\ Inv371_R0_0_I1 /\ Inv1231_R0_0_I1 /\ Safety /\ w1Action => Safety'
       BY DEF TypeOK,Inv1230_R0_0_I1,Inv1470_R0_0_I1,Inv1477_R0_0_I1,Inv32_R0_0_I1,Inv1578_R0_0_I1,Inv370_R0_0_I1,Inv371_R0_0_I1,Inv1231_R0_0_I1,w1Action,w1,Safety,H_MutualExclusion
  \* (Safety,w2Action)
  <1>7. TypeOK /\ Safety /\ w2Action => Safety'
       BY DEF TypeOK,w2Action,w2,Safety,H_MutualExclusion
  \* (Safety,csAction)
  <1>8. TypeOK /\ Safety /\ csAction => Safety'
       BY DEF TypeOK,csAction,cs,Safety,H_MutualExclusion
  \* (Safety,exitAction)
  <1>9. TypeOK /\ Safety /\ exitAction => Safety'
       BY DEF TypeOK,exitAction,exit,Safety,H_MutualExclusion
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1230_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv1230_R0_0_I1 /\ Next => Inv1230_R0_0_I1'
  \* (Inv1230_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1230_R0_0_I1 /\ ncsAction => Inv1230_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1230_R0_0_I1 /\ e1Action => Inv1230_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv1230_R0_0_I1 /\ e2Action => Inv1230_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv1230_R0_0_I1 /\ e3Action => Inv1230_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv1230_R0_0_I1 /\ e4Action => Inv1230_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv1230_R0_0_I1 /\ w1Action => Inv1230_R0_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv1230_R0_0_I1 /\ w2Action => Inv1230_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv1230_R0_0_I1 /\ csAction => Inv1230_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1230_R0_0_I1
  \* (Inv1230_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv1230_R0_0_I1 /\ exitAction => Inv1230_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1230_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1470_R0_0_I1
THEOREM L_3 == TypeOK /\ Inv1477_R0_0_I1 /\ Inv1470_R0_0_I1 /\ Next => Inv1470_R0_0_I1'
  \* (Inv1470_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1470_R0_0_I1 /\ ncsAction => Inv1470_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1470_R0_0_I1 /\ e1Action => Inv1470_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv1470_R0_0_I1 /\ e2Action => Inv1470_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv1470_R0_0_I1 /\ e3Action => Inv1470_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv1470_R0_0_I1 /\ e4Action => Inv1470_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv1477_R0_0_I1 /\ Inv1470_R0_0_I1 /\ w1Action => Inv1470_R0_0_I1'
       BY DEF TypeOK,Inv1477_R0_0_I1,w1Action,w1,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv1470_R0_0_I1 /\ w2Action => Inv1470_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv1470_R0_0_I1 /\ csAction => Inv1470_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1470_R0_0_I1
  \* (Inv1470_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv1470_R0_0_I1 /\ exitAction => Inv1470_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1470_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1477_R0_0_I1
THEOREM L_4 == TypeOK /\ Inv1579_R3_0_I1 /\ Inv1477_R0_0_I1 /\ Next => Inv1477_R0_0_I1'
  \* (Inv1477_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1477_R0_0_I1 /\ ncsAction => Inv1477_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1477_R0_0_I1 /\ e1Action => Inv1477_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv1477_R0_0_I1 /\ e2Action => Inv1477_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv1477_R0_0_I1 /\ e3Action => Inv1477_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv1477_R0_0_I1 /\ e4Action => Inv1477_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv1477_R0_0_I1 /\ w1Action => Inv1477_R0_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv1579_R3_0_I1 /\ Inv1477_R0_0_I1 /\ w2Action => Inv1477_R0_0_I1'
       BY DEF TypeOK,Inv1579_R3_0_I1,w2Action,w2,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv1477_R0_0_I1 /\ csAction => Inv1477_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1477_R0_0_I1
  \* (Inv1477_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv1477_R0_0_I1 /\ exitAction => Inv1477_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1477_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1579_R3_0_I1
THEOREM L_5 == TypeOK /\ Inv1579_R3_0_I1 /\ Next => Inv1579_R3_0_I1'
  \* (Inv1579_R3_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1579_R3_0_I1 /\ ncsAction => Inv1579_R3_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1579_R3_0_I1 /\ e1Action => Inv1579_R3_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,e2Action)
  <1>3. TypeOK /\ Inv1579_R3_0_I1 /\ e2Action => Inv1579_R3_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,e3Action)
  <1>4. TypeOK /\ Inv1579_R3_0_I1 /\ e3Action => Inv1579_R3_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,e4Action)
  <1>5. TypeOK /\ Inv1579_R3_0_I1 /\ e4Action => Inv1579_R3_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,w1Action)
  <1>6. TypeOK /\ Inv1579_R3_0_I1 /\ w1Action => Inv1579_R3_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,w2Action)
  <1>7. TypeOK /\ Inv1579_R3_0_I1 /\ w2Action => Inv1579_R3_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,csAction)
  <1>8. TypeOK /\ Inv1579_R3_0_I1 /\ csAction => Inv1579_R3_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1579_R3_0_I1
  \* (Inv1579_R3_0_I1,exitAction)
  <1>9. TypeOK /\ Inv1579_R3_0_I1 /\ exitAction => Inv1579_R3_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1579_R3_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv32_R0_0_I1
THEOREM L_6 == TypeOK /\ Inv32_R0_0_I1 /\ Next => Inv32_R0_0_I1'
  \* (Inv32_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv32_R0_0_I1 /\ ncsAction => Inv32_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv32_R0_0_I1 /\ e1Action => Inv32_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv32_R0_0_I1 /\ e2Action => Inv32_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv32_R0_0_I1 /\ e3Action => Inv32_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv32_R0_0_I1 /\ e4Action => Inv32_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv32_R0_0_I1 /\ w1Action => Inv32_R0_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv32_R0_0_I1 /\ w2Action => Inv32_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv32_R0_0_I1 /\ csAction => Inv32_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv32_R0_0_I1
  \* (Inv32_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv32_R0_0_I1 /\ exitAction => Inv32_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv32_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1578_R0_0_I1
THEOREM L_7 == TypeOK /\ Inv1578_R0_0_I1 /\ Next => Inv1578_R0_0_I1'
  \* (Inv1578_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv1578_R0_0_I1 /\ ncsAction => Inv1578_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1578_R0_0_I1 /\ e1Action => Inv1578_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv1578_R0_0_I1 /\ e2Action => Inv1578_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv1578_R0_0_I1 /\ e3Action => Inv1578_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv1578_R0_0_I1 /\ e4Action => Inv1578_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv1578_R0_0_I1 /\ w1Action => Inv1578_R0_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv1578_R0_0_I1,
                        TRUE,
                        NEW self \in Procs,
                        w1(self),
                        NEW VARI \in Procs'
                 PROVE  (~(nxt[VARI] = VARI) \/ (~(pc[VARI] = "w2")))'
      BY DEF Inv1578_R0_0_I1, w1Action
    <2> QED
      BY DEF TypeOK,w1Action,w1,Inv1578_R0_0_I1,Procs
       
  \* (Inv1578_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv1578_R0_0_I1 /\ w2Action => Inv1578_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv1578_R0_0_I1 /\ csAction => Inv1578_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1578_R0_0_I1
  \* (Inv1578_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv1578_R0_0_I1 /\ exitAction => Inv1578_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1578_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv370_R0_0_I1
THEOREM L_8 == TypeOK /\ Inv370_R0_0_I1 /\ Next => Inv370_R0_0_I1'
  \* (Inv370_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv370_R0_0_I1 /\ ncsAction => Inv370_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv370_R0_0_I1 /\ e1Action => Inv370_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv370_R0_0_I1 /\ e2Action => Inv370_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv370_R0_0_I1 /\ e3Action => Inv370_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv370_R0_0_I1 /\ e4Action => Inv370_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv370_R0_0_I1 /\ w1Action => Inv370_R0_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv370_R0_0_I1 /\ w2Action => Inv370_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv370_R0_0_I1 /\ csAction => Inv370_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv370_R0_0_I1
  \* (Inv370_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv370_R0_0_I1 /\ exitAction => Inv370_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv370_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv371_R0_0_I1
THEOREM L_9 == TypeOK /\ Inv371_R0_0_I1 /\ Next => Inv371_R0_0_I1'
  \* (Inv371_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv371_R0_0_I1 /\ ncsAction => Inv371_R0_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv371_R0_0_I1 /\ e1Action => Inv371_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv371_R0_0_I1 /\ e2Action => Inv371_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv371_R0_0_I1 /\ e3Action => Inv371_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv371_R0_0_I1 /\ e4Action => Inv371_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv371_R0_0_I1 /\ w1Action => Inv371_R0_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv371_R0_0_I1 /\ w2Action => Inv371_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv371_R0_0_I1 /\ csAction => Inv371_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv371_R0_0_I1
  \* (Inv371_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv371_R0_0_I1 /\ exitAction => Inv371_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv371_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1231_R0_0_I1
THEOREM L_10 == TypeOK /\ Inv521_R8_0_I1 /\ Inv1231_R0_0_I1 /\ Next => Inv1231_R0_0_I1'
  \* (Inv1231_R0_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv521_R8_0_I1 /\ Inv1231_R0_0_I1 /\ ncsAction => Inv1231_R0_0_I1'
       BY DEF TypeOK,Inv521_R8_0_I1,ncsAction,ncs,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,e1Action)
  <1>2. TypeOK /\ Inv1231_R0_0_I1 /\ e1Action => Inv1231_R0_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,e2Action)
  <1>3. TypeOK /\ Inv1231_R0_0_I1 /\ e2Action => Inv1231_R0_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,e3Action)
  <1>4. TypeOK /\ Inv1231_R0_0_I1 /\ e3Action => Inv1231_R0_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,e4Action)
  <1>5. TypeOK /\ Inv1231_R0_0_I1 /\ e4Action => Inv1231_R0_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,w1Action)
  <1>6. TypeOK /\ Inv1231_R0_0_I1 /\ w1Action => Inv1231_R0_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,w2Action)
  <1>7. TypeOK /\ Inv1231_R0_0_I1 /\ w2Action => Inv1231_R0_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,csAction)
  <1>8. TypeOK /\ Inv1231_R0_0_I1 /\ csAction => Inv1231_R0_0_I1'
       BY DEF TypeOK,csAction,cs,Inv1231_R0_0_I1
  \* (Inv1231_R0_0_I1,exitAction)
  <1>9. TypeOK /\ Inv1231_R0_0_I1 /\ exitAction => Inv1231_R0_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv1231_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv521_R8_0_I1
THEOREM L_11 == TypeOK /\ Inv520_R10_0_I1 /\ Inv521_R8_0_I1 /\ Next => Inv521_R8_0_I1'
  \* (Inv521_R8_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv521_R8_0_I1 /\ ncsAction => Inv521_R8_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,e1Action)
  <1>2. TypeOK /\ Inv521_R8_0_I1 /\ e1Action => Inv521_R8_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,e2Action)
  <1>3. TypeOK /\ Inv521_R8_0_I1 /\ e2Action => Inv521_R8_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,e3Action)
  <1>4. TypeOK /\ Inv521_R8_0_I1 /\ e3Action => Inv521_R8_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,e4Action)
  <1>5. TypeOK /\ Inv521_R8_0_I1 /\ e4Action => Inv521_R8_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,w1Action)
  <1>6. TypeOK /\ Inv521_R8_0_I1 /\ w1Action => Inv521_R8_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,w2Action)
  <1>7. TypeOK /\ Inv521_R8_0_I1 /\ w2Action => Inv521_R8_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,csAction)
  <1>8. TypeOK /\ Inv521_R8_0_I1 /\ csAction => Inv521_R8_0_I1'
       BY DEF TypeOK,csAction,cs,Inv521_R8_0_I1
  \* (Inv521_R8_0_I1,exitAction)
  <1>9. TypeOK /\ Inv520_R10_0_I1 /\ Inv521_R8_0_I1 /\ exitAction => Inv521_R8_0_I1'
       BY DEF TypeOK,Inv520_R10_0_I1,exitAction,exit,Inv521_R8_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

ASSUME A1 == N \in Nat
\*** Inv520_R10_0_I1
THEOREM L_12 == TypeOK /\ Inv520_R10_0_I1 /\ Next => Inv520_R10_0_I1'
  \* (Inv520_R10_0_I1,ncsAction)
  <1>1. TypeOK /\ Inv520_R10_0_I1 /\ ncsAction => Inv520_R10_0_I1'
       BY DEF TypeOK,ncsAction,ncs,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,e1Action)
  <1>2. TypeOK /\ Inv520_R10_0_I1 /\ e1Action => Inv520_R10_0_I1'
       BY DEF TypeOK,e1Action,e1,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,e2Action)
  <1>3. TypeOK /\ Inv520_R10_0_I1 /\ e2Action => Inv520_R10_0_I1'
       BY DEF TypeOK,e2Action,e2,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,e3Action)
  <1>4. TypeOK /\ Inv520_R10_0_I1 /\ e3Action => Inv520_R10_0_I1'
       BY DEF TypeOK,e3Action,e3,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,e4Action)
  <1>5. TypeOK /\ Inv520_R10_0_I1 /\ e4Action => Inv520_R10_0_I1'
       BY DEF TypeOK,e4Action,e4,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,w1Action)
  <1>6. TypeOK /\ Inv520_R10_0_I1 /\ w1Action => Inv520_R10_0_I1'
       BY DEF TypeOK,w1Action,w1,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,w2Action)
  <1>7. TypeOK /\ Inv520_R10_0_I1 /\ w2Action => Inv520_R10_0_I1'
       BY DEF TypeOK,w2Action,w2,Inv520_R10_0_I1
  \* (Inv520_R10_0_I1,csAction)
  <1>8. TypeOK /\ Inv520_R10_0_I1 /\ csAction => Inv520_R10_0_I1'
    <2> SUFFICES ASSUME TypeOK /\ Inv520_R10_0_I1 /\ csAction,
                        NEW VARI \in Procs'
                 PROVE  ((unchecked[VARI] = {}) \/ (~(pc[VARI] = "exit")))'
      BY DEF Inv520_R10_0_I1
    <2> QED
      BY A1 DEF TypeOK,csAction,cs,Inv520_R10_0_I1,Procs
       
  \* (Inv520_R10_0_I1,exitAction)
  <1>9. TypeOK /\ Inv520_R10_0_I1 /\ exitAction => Inv520_R10_0_I1'
       BY DEF TypeOK,exitAction,exit,Inv520_R10_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12 DEF Next, IndGlobal




\* Inv21195_R4_0_I3 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARI] = "w1"))
=============================================================================
\* Modification History
\* Last modified Wed Apr 03 02:50:54 EDT 2024 by willyschultz
\* Last modified Tue Dec 18 13:48:46 PST 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
