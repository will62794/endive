------------------------------- MODULE ZeusReliableCommit_IndProofs -------------------------------
EXTENDS ZeusReliableCommit


\* Proof Graph Stats
\* ==================
\* num proof graph nodes: 7
\* num proof obligations: 84
Safety == H_Safety
Inv34_R0_0_I1 == \A VARI \in rAliveNodes : ~(rKeySharers[VARI] = "non-sharer")
Inv1431_R0_1_I1 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : ~(rKeyState[VARI] = "valid") \/ (~(rKeyVersion[VARI] > rKeyVersion[VARJ]))
Inv57_R0_2_I1 == \A VARMINV \in rMsgsINV : ~(VARMINV.version > rKeyVersion[VARMINV.sender])
Inv35_R0_3_I1 == \A VARI \in rAliveNodes : \A VARMVAL \in rMsgsVAL : ~(VARMVAL.type = "VAL" /\ VARMVAL.version > rKeyVersion[VARI])
Inv19115_R0_4_I2 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : (rKeyState[VARI] = "invalid") \/ ((rKeyVersion[VARI] <= rKeyVersion[VARJ])) \/ (~(VARJ \in rKeyRcvedACKs[VARI]))
Inv1153_R5_0_I1 == \A VARJ \in rAliveNodes : \A VARMACK \in rMsgsACK : (VARMACK.version <= rKeyVersion[VARJ]) \/ (~(VARMACK.sender = VARJ))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv34_R0_0_I1
  /\ Inv1431_R0_1_I1
  /\ Inv35_R0_3_I1
  /\ Inv19115_R0_4_I2
  /\ Inv1153_R5_0_I1
  /\ Inv57_R0_2_I1


\* mean in-degree: 0.8571428571428571
\* median in-degree: 1
\* max in-degree: 3
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,RRcvInvAction)
  <1>1. TypeOK /\ TypeOK /\ RRcvInvAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RRcvInvAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (rMsgsINV        \subseteq RMessageINV)'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>2. (rMsgsACK           \subseteq RMessageACK)'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>3. (rMsgsVAL           \subseteq RMessageVAL)'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>4. (rAliveNodes     \subseteq R_NODES)'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>5. (\A n \in R_NODES: rKeyRcvedACKs[n] \subseteq (R_NODES \ {n}))'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>6. (rNodeEpochID    \in [R_NODES -> Nat])'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>7. (rKeyLastWriter  \in [R_NODES -> R_NODES])'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>8. (rKeyVersion     \in [R_NODES -> Nat])'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>9. (rKeySharers     \in [R_NODES -> {"owner", "reader", "non-sharer"}])'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>10. (rKeyState       \in [R_NODES -> {"valid", "invalid", "write", "replay"}])'
      BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
    <2>11. QED
      BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
  \* (TypeOK,RRcvValAction)
  <1>2. TypeOK /\ TypeOK /\ RRcvValAction => TypeOK'
       BY DEF TypeOK,RRcvValAction,RRcvVal,TypeOK
  \* (TypeOK,RReadAction)
  <1>3. TypeOK /\ TypeOK /\ RReadAction => TypeOK'
       BY DEF TypeOK,RReadAction,RRead,TypeOK
  \* (TypeOK,RWriteAction)
  <1>4. TypeOK /\ TypeOK /\ RWriteAction => TypeOK'
       BY DEF TypeOK,RWriteAction,RWrite,TypeOK
  \* (TypeOK,RRcvAckAction)
  <1>5. TypeOK /\ TypeOK /\ RRcvAckAction => TypeOK'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,TypeOK
  \* (TypeOK,RSendValsAction)
  <1>6. TypeOK /\ TypeOK /\ RSendValsAction => TypeOK'
       BY DEF TypeOK,RSendValsAction,RSendVals,TypeOK
  \* (TypeOK,RLocalWriteReplayAction)
  <1>7. TypeOK /\ TypeOK /\ RLocalWriteReplayAction => TypeOK'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,TypeOK
  \* (TypeOK,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ TypeOK /\ RFailedNodeWriteReplayAction => TypeOK'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,TypeOK
  \* (TypeOK,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ TypeOK /\ RUpdateLocalEpochIDAction => TypeOK'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,TypeOK
  \* (TypeOK,ROverthrowOwnerAction)
  <1>10. TypeOK /\ TypeOK /\ ROverthrowOwnerAction => TypeOK'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,TypeOK
  \* (TypeOK,RNewOwnerAction)
  <1>11. TypeOK /\ TypeOK /\ RNewOwnerAction => TypeOK'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,TypeOK
  \* (TypeOK,RNodeFailureAction)
  <1>12. TypeOK /\ TypeOK /\ RNodeFailureAction => TypeOK'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,TypeOK
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv57_R0_2_I1 /\ Inv1431_R0_1_I1 /\ Inv34_R0_0_I1 /\ Safety /\ Next => Safety'
  \* (Safety,RRcvInvAction)
  <1>1. TypeOK /\ Inv57_R0_2_I1 /\ Safety /\ RRcvInvAction => Safety'
       BY DEF TypeOK,Inv57_R0_2_I1,RRcvInvAction,RRcvInv,Safety,RConsistentInvariant
  \* (Safety,RRcvValAction)
  <1>2. TypeOK /\ Safety /\ RRcvValAction => Safety'
       BY DEF TypeOK,RRcvValAction,RRcvVal,Safety,RConsistentInvariant
  \* (Safety,RReadAction)
  <1>3. TypeOK /\ Safety /\ RReadAction => Safety'
       BY DEF TypeOK,RReadAction,RRead,Safety,RConsistentInvariant
  \* (Safety,RWriteAction)
  <1>4. TypeOK /\ Safety /\ RWriteAction => Safety'
       BY DEF TypeOK,RWriteAction,RWrite,Safety,RConsistentInvariant
  \* (Safety,RRcvAckAction)
  <1>5. TypeOK /\ Safety /\ RRcvAckAction => Safety'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,Safety,RConsistentInvariant
  \* (Safety,RSendValsAction)
  <1>6. TypeOK /\ Safety /\ RSendValsAction => Safety'
       BY DEF TypeOK,RSendValsAction,RSendVals,Safety,RConsistentInvariant
  \* (Safety,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Safety /\ RLocalWriteReplayAction => Safety'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Safety,RConsistentInvariant
  \* (Safety,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Safety /\ RFailedNodeWriteReplayAction => Safety'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Safety,RConsistentInvariant
  \* (Safety,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Safety /\ RUpdateLocalEpochIDAction => Safety'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Safety,RConsistentInvariant
  \* (Safety,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv1431_R0_1_I1 /\ Safety /\ ROverthrowOwnerAction => Safety'
       BY DEF TypeOK,Inv1431_R0_1_I1,ROverthrowOwnerAction,ROverthrowOwner,Safety,RConsistentInvariant
  \* (Safety,RNewOwnerAction)
  <1>11. TypeOK /\ Inv34_R0_0_I1 /\ Safety /\ RNewOwnerAction => Safety'
       BY DEF TypeOK,Inv34_R0_0_I1,RNewOwnerAction,RNewOwner,Safety,RConsistentInvariant
  \* (Safety,RNodeFailureAction)
  <1>12. TypeOK /\ Safety /\ RNodeFailureAction => Safety'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Safety,RConsistentInvariant
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv34_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv34_R0_0_I1 /\ Next => Inv34_R0_0_I1'
  \* (Inv34_R0_0_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv34_R0_0_I1 /\ RRcvInvAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv34_R0_0_I1 /\ RRcvValAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RRcvValAction,RRcvVal,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RReadAction)
  <1>3. TypeOK /\ Inv34_R0_0_I1 /\ RReadAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RReadAction,RRead,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RWriteAction)
  <1>4. TypeOK /\ Inv34_R0_0_I1 /\ RWriteAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RWriteAction,RWrite,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RRcvAckAction)
  <1>5. TypeOK /\ Inv34_R0_0_I1 /\ RRcvAckAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RSendValsAction)
  <1>6. TypeOK /\ Inv34_R0_0_I1 /\ RSendValsAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RSendValsAction,RSendVals,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Inv34_R0_0_I1 /\ RLocalWriteReplayAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Inv34_R0_0_I1 /\ RFailedNodeWriteReplayAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Inv34_R0_0_I1 /\ RUpdateLocalEpochIDAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv34_R0_0_I1 /\ ROverthrowOwnerAction => Inv34_R0_0_I1'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RNewOwnerAction)
  <1>11. TypeOK /\ Inv34_R0_0_I1 /\ RNewOwnerAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv34_R0_0_I1
  \* (Inv34_R0_0_I1,RNodeFailureAction)
  <1>12. TypeOK /\ Inv34_R0_0_I1 /\ RNodeFailureAction => Inv34_R0_0_I1'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv34_R0_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1431_R0_1_I1
THEOREM L_3 == TypeOK /\ Inv35_R0_3_I1 /\ Inv1431_R0_1_I1 /\ Next => Inv1431_R0_1_I1'
  \* (Inv1431_R0_1_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv1431_R0_1_I1 /\ RRcvInvAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv35_R0_3_I1 /\ Inv1431_R0_1_I1 /\ RRcvValAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,Inv35_R0_3_I1,RRcvValAction,RRcvVal,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RReadAction)
  <1>3. TypeOK /\ Inv1431_R0_1_I1 /\ RReadAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RReadAction,RRead,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RWriteAction)
  <1>4. TypeOK /\ Inv1431_R0_1_I1 /\ RWriteAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RWriteAction,RWrite,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RRcvAckAction)
  <1>5. TypeOK /\ Inv1431_R0_1_I1 /\ RRcvAckAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RSendValsAction)
  <1>6. TypeOK /\ Inv1431_R0_1_I1 /\ RSendValsAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RSendValsAction,RSendVals,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Inv1431_R0_1_I1 /\ RLocalWriteReplayAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Inv1431_R0_1_I1 /\ RFailedNodeWriteReplayAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Inv1431_R0_1_I1 /\ RUpdateLocalEpochIDAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv1431_R0_1_I1 /\ ROverthrowOwnerAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RNewOwnerAction)
  <1>11. TypeOK /\ Inv1431_R0_1_I1 /\ RNewOwnerAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv1431_R0_1_I1
  \* (Inv1431_R0_1_I1,RNodeFailureAction)
  <1>12. TypeOK /\ Inv1431_R0_1_I1 /\ RNodeFailureAction => Inv1431_R0_1_I1'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv1431_R0_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv35_R0_3_I1
THEOREM L_4 == TypeOK /\ Inv19115_R0_4_I2 /\ Inv35_R0_3_I1 /\ Next => Inv35_R0_3_I1'
  \* (Inv35_R0_3_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv35_R0_3_I1 /\ RRcvInvAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv35_R0_3_I1 /\ RRcvValAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RRcvValAction,RRcvVal,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RReadAction)
  <1>3. TypeOK /\ Inv35_R0_3_I1 /\ RReadAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RReadAction,RRead,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RWriteAction)
  <1>4. TypeOK /\ Inv35_R0_3_I1 /\ RWriteAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RWriteAction,RWrite,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RRcvAckAction)
  <1>5. TypeOK /\ Inv35_R0_3_I1 /\ RRcvAckAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RSendValsAction)
  <1>6. TypeOK /\ Inv19115_R0_4_I2 /\ Inv35_R0_3_I1 /\ RSendValsAction => Inv35_R0_3_I1'
       BY DEF TypeOK,Inv19115_R0_4_I2,RSendValsAction,RSendVals,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Inv35_R0_3_I1 /\ RLocalWriteReplayAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Inv35_R0_3_I1 /\ RFailedNodeWriteReplayAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Inv35_R0_3_I1 /\ RUpdateLocalEpochIDAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv35_R0_3_I1 /\ ROverthrowOwnerAction => Inv35_R0_3_I1'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RNewOwnerAction)
  <1>11. TypeOK /\ Inv35_R0_3_I1 /\ RNewOwnerAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv35_R0_3_I1
  \* (Inv35_R0_3_I1,RNodeFailureAction)
  <1>12. TypeOK /\ Inv35_R0_3_I1 /\ RNodeFailureAction => Inv35_R0_3_I1'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv35_R0_3_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv19115_R0_4_I2
THEOREM L_5 == TypeOK /\ Inv1153_R5_0_I1 /\ Inv19115_R0_4_I2 /\ Next => Inv19115_R0_4_I2'
  \* (Inv19115_R0_4_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv19115_R0_4_I2 /\ RRcvInvAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv19115_R0_4_I2 /\ RRcvValAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RRcvValAction,RRcvVal,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RReadAction)
  <1>3. TypeOK /\ Inv19115_R0_4_I2 /\ RReadAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RReadAction,RRead,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RWriteAction)
  <1>4. TypeOK /\ Inv19115_R0_4_I2 /\ RWriteAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RWriteAction,RWrite,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RRcvAckAction)
  <1>5. TypeOK /\ Inv1153_R5_0_I1 /\ Inv19115_R0_4_I2 /\ RRcvAckAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,Inv1153_R5_0_I1,RRcvAckAction,RRcvAck,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RSendValsAction)
  <1>6. TypeOK /\ Inv19115_R0_4_I2 /\ RSendValsAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RSendValsAction,RSendVals,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Inv19115_R0_4_I2 /\ RLocalWriteReplayAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Inv19115_R0_4_I2 /\ RFailedNodeWriteReplayAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Inv19115_R0_4_I2 /\ RUpdateLocalEpochIDAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv19115_R0_4_I2 /\ ROverthrowOwnerAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RNewOwnerAction)
  <1>11. TypeOK /\ Inv19115_R0_4_I2 /\ RNewOwnerAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv19115_R0_4_I2
  \* (Inv19115_R0_4_I2,RNodeFailureAction)
  <1>12. TypeOK /\ Inv19115_R0_4_I2 /\ RNodeFailureAction => Inv19115_R0_4_I2'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv19115_R0_4_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1153_R5_0_I1
THEOREM L_6 == TypeOK /\ Inv1153_R5_0_I1 /\ Next => Inv1153_R5_0_I1'
  \* (Inv1153_R5_0_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv1153_R5_0_I1 /\ RRcvInvAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv1153_R5_0_I1 /\ RRcvValAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RRcvValAction,RRcvVal,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RReadAction)
  <1>3. TypeOK /\ Inv1153_R5_0_I1 /\ RReadAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RReadAction,RRead,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RWriteAction)
  <1>4. TypeOK /\ Inv1153_R5_0_I1 /\ RWriteAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RWriteAction,RWrite,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RRcvAckAction)
  <1>5. TypeOK /\ Inv1153_R5_0_I1 /\ RRcvAckAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RSendValsAction)
  <1>6. TypeOK /\ Inv1153_R5_0_I1 /\ RSendValsAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RSendValsAction,RSendVals,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Inv1153_R5_0_I1 /\ RLocalWriteReplayAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Inv1153_R5_0_I1 /\ RFailedNodeWriteReplayAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Inv1153_R5_0_I1 /\ RUpdateLocalEpochIDAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv1153_R5_0_I1 /\ ROverthrowOwnerAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RNewOwnerAction)
  <1>11. TypeOK /\ Inv1153_R5_0_I1 /\ RNewOwnerAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv1153_R5_0_I1
  \* (Inv1153_R5_0_I1,RNodeFailureAction)
  <1>12. TypeOK /\ Inv1153_R5_0_I1 /\ RNodeFailureAction => Inv1153_R5_0_I1'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv1153_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv57_R0_2_I1
THEOREM L_7 == TypeOK /\ Inv57_R0_2_I1 /\ Next => Inv57_R0_2_I1'
  \* (Inv57_R0_2_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv57_R0_2_I1 /\ RRcvInvAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv57_R0_2_I1 /\ RRcvValAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RRcvValAction,RRcvVal,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RReadAction)
  <1>3. TypeOK /\ Inv57_R0_2_I1 /\ RReadAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RReadAction,RRead,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RWriteAction)
  <1>4. TypeOK /\ Inv57_R0_2_I1 /\ RWriteAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RWriteAction,RWrite,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RRcvAckAction)
  <1>5. TypeOK /\ Inv57_R0_2_I1 /\ RRcvAckAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RSendValsAction)
  <1>6. TypeOK /\ Inv57_R0_2_I1 /\ RSendValsAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RSendValsAction,RSendVals,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RLocalWriteReplayAction)
  <1>7. TypeOK /\ Inv57_R0_2_I1 /\ RLocalWriteReplayAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RFailedNodeWriteReplayAction)
  <1>8. TypeOK /\ Inv57_R0_2_I1 /\ RFailedNodeWriteReplayAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RUpdateLocalEpochIDAction)
  <1>9. TypeOK /\ Inv57_R0_2_I1 /\ RUpdateLocalEpochIDAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,ROverthrowOwnerAction)
  <1>10. TypeOK /\ Inv57_R0_2_I1 /\ ROverthrowOwnerAction => Inv57_R0_2_I1'
       BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RNewOwnerAction)
  <1>11. TypeOK /\ Inv57_R0_2_I1 /\ RNewOwnerAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv57_R0_2_I1
  \* (Inv57_R0_2_I1,RNodeFailureAction)
  <1>12. TypeOK /\ Inv57_R0_2_I1 /\ RNodeFailureAction => Inv57_R0_2_I1'
       BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv57_R0_2_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7 DEF Next, IndGlobal


=============================================================================
