------------------------------- MODULE ZeusReliableCommit_IndProofs -------------------------------
EXTENDS ZeusReliableCommit, FiniteSetTheorems

\* Proof Graph Stats
\* ==================
\* seed: 2
\* num proof graph nodes: 15
\* num proof obligations: 165
Safety == RConsistentInvariant
Inv29_R0_0_I1 == \A VARI \in rAliveNodes : \A VARMVAL \in rMsgsVAL : ~(VARMVAL.type = "VAL" /\ VARMVAL.version > rKeyVersion[VARI])
Inv602_R0_0_I1 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : (rKeyVersion[VARI] <= rKeyVersion[VARJ]) \/ (~(rKeyState[VARI] = "valid"))
Inv15995_R0_1_I2 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : ~(VARJ \in rKeyRcvedACKs[VARI]) \/ (~(rKeyState[VARI] \in {"write", "replay"})) \/ (~(rKeyVersion[VARI] > rKeyVersion[VARJ]))
Inv326_R0_1_I2 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : (rKeyVersion[VARI] <= rKeyVersion[VARJ]) \/ (~(rKeyState[VARJ] = "write"))
Inv407_R0_1_I2 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : ~(VARI # VARJ /\ rKeyState[VARI] = "write") \/ (~(rKeyState[VARJ] = "write"))
Inv794_R3_0_I1 == \A VARJ \in rAliveNodes : \A VARMACK \in rMsgsACK : (VARMACK.version <= rKeyVersion[VARJ]) \/ (~(VARMACK.sender = VARJ))
Inv30_R4_0_I0 == \A VARMINV \in rMsgsINV : ~(VARMINV.version > rKeyVersion[VARMINV.sender])
Inv12_R4_1_I1 == \A VARI \in rAliveNodes : ~(rKeySharers[VARI] = "non-sharer")
Inv356_R4_1_I1 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : (rKeySharers[VARJ] = "reader") \/ ((rKeyVersion[VARI] <= rKeyVersion[VARJ]))
Inv234_R4_1_I1 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : (rKeySharers[VARI] = "reader") \/ (~(VARI # VARJ /\ rKeyState[VARJ] = "write"))
Inv27_R9_1_I1 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : ~(rKeyState[VARI] = "valid") \/ (~(rKeyVersion[VARI] > rKeyVersion[VARJ]))
Inv82_R9_3_I2 == \A VARI \in rAliveNodes : (rNodeEpochID[VARI] < rEpochID) \/ ((rNodeEpochID[VARI] = rEpochID))
Inv4413_R9_3_I2 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : (rKeySharers[VARJ] = "reader") \/ (~(VARI # VARJ /\ rKeyState = rKeyState) \/ (~(rKeySharers[VARI] = "owner")))
Inv85_R9_3_I2 == \A VARI \in rAliveNodes : (rNodeEpochID[VARI] < rEpochID) \/ (~(rKeyState[VARI] = "replay"))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv29_R0_0_I1
  /\ Inv15995_R0_1_I2
  /\ Inv794_R3_0_I1
  /\ Inv326_R0_1_I2
  /\ Inv30_R4_0_I0
  /\ Inv12_R4_1_I1
  /\ Inv356_R4_1_I1
  /\ Inv602_R0_0_I1
  /\ Inv27_R9_1_I1
  /\ Inv234_R4_1_I1
  /\ Inv4413_R9_3_I2
  /\ Inv82_R9_3_I2
  /\ Inv85_R9_3_I2
  /\ Inv407_R0_1_I2


\* mean in-degree: 2.3333333333333335
\* median in-degree: 1
\* max in-degree: 10
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(R_NODES)
ASSUME A1 == R_NODES \subseteq Nat

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1
  \* (TypeOK,RRcvInvAction)
  <1>1. TypeOK /\ TypeOK /\ RRcvInvAction => TypeOK' BY DEF TypeOK,RRcvInvAction,RRcvInv,TypeOK
  \* (TypeOK,RRcvValAction)
  <1>2. TypeOK /\ TypeOK /\ RRcvValAction => TypeOK' BY DEF TypeOK,RRcvValAction,RRcvVal,TypeOK
  \* (TypeOK,RWriteAction)
  <1>3. TypeOK /\ TypeOK /\ RWriteAction => TypeOK' BY DEF TypeOK,RWriteAction,RWrite,TypeOK,RMessageINV,RMessageVAL
  \* (TypeOK,RRcvAckAction)
  <1>4. TypeOK /\ TypeOK /\ RRcvAckAction => TypeOK' BY DEF TypeOK,RRcvAckAction,RRcvAck,TypeOK
  \* (TypeOK,RSendValsAction)
  <1>5. TypeOK /\ TypeOK /\ RSendValsAction => TypeOK' BY DEF TypeOK,RSendValsAction,RSendVals,TypeOK
  \* (TypeOK,RLocalWriteReplayAction)
  <1>6. TypeOK /\ TypeOK /\ RLocalWriteReplayAction => TypeOK' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,TypeOK
  \* (TypeOK,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ TypeOK /\ RFailedNodeWriteReplayAction => TypeOK' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,TypeOK
  \* (TypeOK,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ TypeOK /\ RUpdateLocalEpochIDAction => TypeOK' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,TypeOK
  \* (TypeOK,ROverthrowOwnerAction)
  <1>9. TypeOK /\ TypeOK /\ ROverthrowOwnerAction => TypeOK' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,TypeOK
  \* (TypeOK,RNewOwnerAction)
  <1>10. TypeOK /\ TypeOK /\ RNewOwnerAction => TypeOK' BY DEF TypeOK,RNewOwnerAction,RNewOwner,TypeOK
  \* (TypeOK,RNodeFailureAction)
  <1>11. TypeOK /\ TypeOK /\ RNodeFailureAction => TypeOK' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,TypeOK,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv29_R0_0_I1 /\ Inv602_R0_0_I1 /\ Inv602_R0_0_I1 /\ Inv15995_R0_1_I2 /\ Inv326_R0_1_I2 /\ Inv407_R0_1_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1
  \* (Safety,RRcvInvAction)
  <1>1. TypeOK /\ Safety /\ RRcvInvAction => Safety' BY DEF TypeOK,RRcvInvAction,RRcvInv,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RRcvValAction)
  <1>2. TypeOK /\ Inv29_R0_0_I1 /\ Inv602_R0_0_I1 /\ Safety /\ RRcvValAction => Safety' BY DEF TypeOK,Inv29_R0_0_I1,Inv602_R0_0_I1,RRcvValAction,RRcvVal,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RWriteAction)
  <1>3. TypeOK /\ Safety /\ RWriteAction => Safety' BY DEF TypeOK,RWriteAction,RWrite,Safety,RMessageINV,RMessageVAL,RConsistentInvariant,RMessageINV
  \* (Safety,RRcvAckAction)
  <1>4. TypeOK /\ Safety /\ RRcvAckAction => Safety' BY DEF TypeOK,RRcvAckAction,RRcvAck,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RSendValsAction)
  <1>5. TypeOK /\ Inv602_R0_0_I1 /\ Inv15995_R0_1_I2 /\ Inv326_R0_1_I2 /\ Inv407_R0_1_I2 /\ Safety /\ RSendValsAction => Safety' BY DEF TypeOK,Inv602_R0_0_I1,Inv15995_R0_1_I2,Inv326_R0_1_I2,Inv407_R0_1_I2,RSendValsAction,RSendVals,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Safety /\ RLocalWriteReplayAction => Safety' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Safety /\ RFailedNodeWriteReplayAction => Safety' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Safety /\ RUpdateLocalEpochIDAction => Safety' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Safety /\ ROverthrowOwnerAction => Safety' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RNewOwnerAction)
  <1>10. TypeOK /\ Safety /\ RNewOwnerAction => Safety' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Safety,RConsistentInvariant,RMessageINV
  \* (Safety,RNodeFailureAction)
  <1>11. TypeOK /\ Safety /\ RNodeFailureAction => Safety' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Safety,RMessageINV,RNoChanges_but_membership,RConsistentInvariant,RMessageINV
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv29_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv15995_R0_1_I2 /\ Inv29_R0_0_I1 /\ Next => Inv29_R0_0_I1'
  <1>. USE A0,A1
  \* (Inv29_R0_0_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv29_R0_0_I1 /\ RRcvInvAction => Inv29_R0_0_I1' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv29_R0_0_I1 /\ RRcvValAction => Inv29_R0_0_I1' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RWriteAction)
  <1>3. TypeOK /\ Inv29_R0_0_I1 /\ RWriteAction => Inv29_R0_0_I1' BY DEF TypeOK,RWriteAction,RWrite,Inv29_R0_0_I1,RMessageINV,RMessageVAL
  \* (Inv29_R0_0_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv29_R0_0_I1 /\ RRcvAckAction => Inv29_R0_0_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv15995_R0_1_I2 /\ Inv29_R0_0_I1 /\ RSendValsAction => Inv29_R0_0_I1' BY DEF TypeOK,Inv15995_R0_1_I2,RSendValsAction,RSendVals,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv29_R0_0_I1 /\ RLocalWriteReplayAction => Inv29_R0_0_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv29_R0_0_I1 /\ RFailedNodeWriteReplayAction => Inv29_R0_0_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv29_R0_0_I1 /\ RUpdateLocalEpochIDAction => Inv29_R0_0_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv29_R0_0_I1 /\ ROverthrowOwnerAction => Inv29_R0_0_I1' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv29_R0_0_I1 /\ RNewOwnerAction => Inv29_R0_0_I1' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv29_R0_0_I1
  \* (Inv29_R0_0_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv29_R0_0_I1 /\ RNodeFailureAction => Inv29_R0_0_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv29_R0_0_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv15995_R0_1_I2
THEOREM L_3 == TypeOK /\ Inv794_R3_0_I1 /\ Inv326_R0_1_I2 /\ Inv602_R0_0_I1 /\ Inv407_R0_1_I2 /\ Inv15995_R0_1_I2 /\ Next => Inv15995_R0_1_I2'
  <1>. USE A0,A1
  \* (Inv15995_R0_1_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv15995_R0_1_I2 /\ RRcvInvAction => Inv15995_R0_1_I2' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv15995_R0_1_I2 /\ RRcvValAction => Inv15995_R0_1_I2' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RWriteAction)
  <1>3. TypeOK /\ Inv15995_R0_1_I2 /\ RWriteAction => Inv15995_R0_1_I2' BY DEF TypeOK,RWriteAction,RWrite,Inv15995_R0_1_I2,RMessageINV,RMessageVAL
  \* (Inv15995_R0_1_I2,RRcvAckAction)
  <1>4. TypeOK /\ Inv794_R3_0_I1 /\ Inv326_R0_1_I2 /\ Inv602_R0_0_I1 /\ Inv407_R0_1_I2 /\ Inv15995_R0_1_I2 /\ RRcvAckAction => Inv15995_R0_1_I2' BY DEF TypeOK,Inv794_R3_0_I1,Inv326_R0_1_I2,Inv602_R0_0_I1,Inv407_R0_1_I2,RRcvAckAction,RRcvAck,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RSendValsAction)
  <1>5. TypeOK /\ Inv15995_R0_1_I2 /\ RSendValsAction => Inv15995_R0_1_I2' BY DEF TypeOK,RSendValsAction,RSendVals,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv15995_R0_1_I2 /\ RLocalWriteReplayAction => Inv15995_R0_1_I2' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv15995_R0_1_I2 /\ RFailedNodeWriteReplayAction => Inv15995_R0_1_I2' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv15995_R0_1_I2 /\ RUpdateLocalEpochIDAction => Inv15995_R0_1_I2' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv15995_R0_1_I2 /\ ROverthrowOwnerAction => Inv15995_R0_1_I2' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RNewOwnerAction)
  <1>10. TypeOK /\ Inv15995_R0_1_I2 /\ RNewOwnerAction => Inv15995_R0_1_I2' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv15995_R0_1_I2
  \* (Inv15995_R0_1_I2,RNodeFailureAction)
  <1>11. TypeOK /\ Inv15995_R0_1_I2 /\ RNodeFailureAction => Inv15995_R0_1_I2' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv15995_R0_1_I2,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv794_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv794_R3_0_I1 /\ Next => Inv794_R3_0_I1'
  <1>. USE A0,A1
  \* (Inv794_R3_0_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv794_R3_0_I1 /\ RRcvInvAction => Inv794_R3_0_I1' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv794_R3_0_I1 /\ RRcvValAction => Inv794_R3_0_I1' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RWriteAction)
  <1>3. TypeOK /\ Inv794_R3_0_I1 /\ RWriteAction => Inv794_R3_0_I1' BY DEF TypeOK,RWriteAction,RWrite,Inv794_R3_0_I1,RMessageINV,RMessageVAL
  \* (Inv794_R3_0_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv794_R3_0_I1 /\ RRcvAckAction => Inv794_R3_0_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv794_R3_0_I1 /\ RSendValsAction => Inv794_R3_0_I1' BY DEF TypeOK,RSendValsAction,RSendVals,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv794_R3_0_I1 /\ RLocalWriteReplayAction => Inv794_R3_0_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv794_R3_0_I1 /\ RFailedNodeWriteReplayAction => Inv794_R3_0_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv794_R3_0_I1 /\ RUpdateLocalEpochIDAction => Inv794_R3_0_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv794_R3_0_I1 /\ ROverthrowOwnerAction => Inv794_R3_0_I1' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv794_R3_0_I1 /\ RNewOwnerAction => Inv794_R3_0_I1' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv794_R3_0_I1
  \* (Inv794_R3_0_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv794_R3_0_I1 /\ RNodeFailureAction => Inv794_R3_0_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv794_R3_0_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv326_R0_1_I2
THEOREM L_5 == TypeOK /\ Inv30_R4_0_I0 /\ Inv12_R4_1_I1 /\ Inv356_R4_1_I1 /\ Inv602_R0_0_I1 /\ Inv234_R4_1_I1 /\ Inv407_R0_1_I2 /\ Inv326_R0_1_I2 /\ Next => Inv326_R0_1_I2'
  <1>. USE A0,A1
  \* (Inv326_R0_1_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv30_R4_0_I0 /\ Inv326_R0_1_I2 /\ RRcvInvAction => Inv326_R0_1_I2' BY DEF TypeOK,Inv30_R4_0_I0,RRcvInvAction,RRcvInv,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv326_R0_1_I2 /\ RRcvValAction => Inv326_R0_1_I2' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RWriteAction)
  <1>3. TypeOK /\ Inv12_R4_1_I1 /\ Inv356_R4_1_I1 /\ Inv602_R0_0_I1 /\ Inv234_R4_1_I1 /\ Inv407_R0_1_I2 /\ Inv326_R0_1_I2 /\ RWriteAction => Inv326_R0_1_I2' BY DEF TypeOK,Inv12_R4_1_I1,Inv356_R4_1_I1,Inv602_R0_0_I1,Inv234_R4_1_I1,Inv407_R0_1_I2,RWriteAction,RWrite,Inv326_R0_1_I2,RMessageINV,RMessageVAL
  \* (Inv326_R0_1_I2,RRcvAckAction)
  <1>4. TypeOK /\ Inv326_R0_1_I2 /\ RRcvAckAction => Inv326_R0_1_I2' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RSendValsAction)
  <1>5. TypeOK /\ Inv326_R0_1_I2 /\ RSendValsAction => Inv326_R0_1_I2' BY DEF TypeOK,RSendValsAction,RSendVals,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv326_R0_1_I2 /\ RLocalWriteReplayAction => Inv326_R0_1_I2' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv326_R0_1_I2 /\ RFailedNodeWriteReplayAction => Inv326_R0_1_I2' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv326_R0_1_I2 /\ RUpdateLocalEpochIDAction => Inv326_R0_1_I2' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv326_R0_1_I2 /\ ROverthrowOwnerAction => Inv326_R0_1_I2' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RNewOwnerAction)
  <1>10. TypeOK /\ Inv326_R0_1_I2 /\ RNewOwnerAction => Inv326_R0_1_I2' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv326_R0_1_I2
  \* (Inv326_R0_1_I2,RNodeFailureAction)
  <1>11. TypeOK /\ Inv326_R0_1_I2 /\ RNodeFailureAction => Inv326_R0_1_I2' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv326_R0_1_I2,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv30_R4_0_I0
THEOREM L_6 == TypeOK /\ Inv30_R4_0_I0 /\ Next => Inv30_R4_0_I0'
  <1>. USE A0,A1
  \* (Inv30_R4_0_I0,RRcvInvAction)
  <1>1. TypeOK /\ Inv30_R4_0_I0 /\ RRcvInvAction => Inv30_R4_0_I0' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RRcvValAction)
  <1>2. TypeOK /\ Inv30_R4_0_I0 /\ RRcvValAction => Inv30_R4_0_I0' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RWriteAction)
  <1>3. TypeOK /\ Inv30_R4_0_I0 /\ RWriteAction => Inv30_R4_0_I0' BY DEF TypeOK,RWriteAction,RWrite,Inv30_R4_0_I0,RMessageINV,RMessageVAL
  \* (Inv30_R4_0_I0,RRcvAckAction)
  <1>4. TypeOK /\ Inv30_R4_0_I0 /\ RRcvAckAction => Inv30_R4_0_I0' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RSendValsAction)
  <1>5. TypeOK /\ Inv30_R4_0_I0 /\ RSendValsAction => Inv30_R4_0_I0' BY DEF TypeOK,RSendValsAction,RSendVals,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv30_R4_0_I0 /\ RLocalWriteReplayAction => Inv30_R4_0_I0' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv30_R4_0_I0 /\ RFailedNodeWriteReplayAction => Inv30_R4_0_I0' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv30_R4_0_I0 /\ RUpdateLocalEpochIDAction => Inv30_R4_0_I0' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv30_R4_0_I0 /\ ROverthrowOwnerAction => Inv30_R4_0_I0' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RNewOwnerAction)
  <1>10. TypeOK /\ Inv30_R4_0_I0 /\ RNewOwnerAction => Inv30_R4_0_I0' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv30_R4_0_I0
  \* (Inv30_R4_0_I0,RNodeFailureAction)
  <1>11. TypeOK /\ Inv30_R4_0_I0 /\ RNodeFailureAction => Inv30_R4_0_I0' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv30_R4_0_I0,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv12_R4_1_I1
THEOREM L_7 == TypeOK /\ Inv12_R4_1_I1 /\ Next => Inv12_R4_1_I1'
  <1>. USE A0,A1
  \* (Inv12_R4_1_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv12_R4_1_I1 /\ RRcvInvAction => Inv12_R4_1_I1' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv12_R4_1_I1 /\ RRcvValAction => Inv12_R4_1_I1' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RWriteAction)
  <1>3. TypeOK /\ Inv12_R4_1_I1 /\ RWriteAction => Inv12_R4_1_I1' BY DEF TypeOK,RWriteAction,RWrite,Inv12_R4_1_I1,RMessageINV,RMessageVAL
  \* (Inv12_R4_1_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv12_R4_1_I1 /\ RRcvAckAction => Inv12_R4_1_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv12_R4_1_I1 /\ RSendValsAction => Inv12_R4_1_I1' BY DEF TypeOK,RSendValsAction,RSendVals,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv12_R4_1_I1 /\ RLocalWriteReplayAction => Inv12_R4_1_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv12_R4_1_I1 /\ RFailedNodeWriteReplayAction => Inv12_R4_1_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv12_R4_1_I1 /\ RUpdateLocalEpochIDAction => Inv12_R4_1_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv12_R4_1_I1 /\ ROverthrowOwnerAction => Inv12_R4_1_I1' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv12_R4_1_I1 /\ RNewOwnerAction => Inv12_R4_1_I1' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv12_R4_1_I1
  \* (Inv12_R4_1_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv12_R4_1_I1 /\ RNodeFailureAction => Inv12_R4_1_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv12_R4_1_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv356_R4_1_I1
THEOREM L_8 == TypeOK /\ Inv30_R4_0_I0 /\ Inv12_R4_1_I1 /\ Inv234_R4_1_I1 /\ Inv82_R9_3_I2 /\ Inv4413_R9_3_I2 /\ Inv602_R0_0_I1 /\ Inv85_R9_3_I2 /\ Inv27_R9_1_I1 /\ Inv12_R4_1_I1 /\ Inv602_R0_0_I1 /\ Inv356_R4_1_I1 /\ Next => Inv356_R4_1_I1'
  <1>. USE A0,A1
  \* (Inv356_R4_1_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv30_R4_0_I0 /\ Inv356_R4_1_I1 /\ RRcvInvAction => Inv356_R4_1_I1' BY DEF TypeOK,Inv30_R4_0_I0,RRcvInvAction,RRcvInv,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv356_R4_1_I1 /\ RRcvValAction => Inv356_R4_1_I1' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RWriteAction)
  <1>3. TypeOK /\ Inv12_R4_1_I1 /\ Inv234_R4_1_I1 /\ Inv82_R9_3_I2 /\ Inv4413_R9_3_I2 /\ Inv602_R0_0_I1 /\ Inv85_R9_3_I2 /\ Inv356_R4_1_I1 /\ RWriteAction => Inv356_R4_1_I1' BY DEF TypeOK,Inv12_R4_1_I1,Inv234_R4_1_I1,Inv82_R9_3_I2,Inv4413_R9_3_I2,Inv602_R0_0_I1,Inv85_R9_3_I2,RWriteAction,RWrite,Inv356_R4_1_I1,RMessageINV,RMessageVAL
  \* (Inv356_R4_1_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv356_R4_1_I1 /\ RRcvAckAction => Inv356_R4_1_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv356_R4_1_I1 /\ RSendValsAction => Inv356_R4_1_I1' BY DEF TypeOK,RSendValsAction,RSendVals,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv356_R4_1_I1 /\ RLocalWriteReplayAction => Inv356_R4_1_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv356_R4_1_I1 /\ RFailedNodeWriteReplayAction => Inv356_R4_1_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv356_R4_1_I1 /\ RUpdateLocalEpochIDAction => Inv356_R4_1_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv27_R9_1_I1 /\ Inv356_R4_1_I1 /\ ROverthrowOwnerAction => Inv356_R4_1_I1' BY DEF TypeOK,Inv27_R9_1_I1,ROverthrowOwnerAction,ROverthrowOwner,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv12_R4_1_I1 /\ Inv602_R0_0_I1 /\ Inv356_R4_1_I1 /\ RNewOwnerAction => Inv356_R4_1_I1' BY DEF TypeOK,Inv12_R4_1_I1,Inv602_R0_0_I1,RNewOwnerAction,RNewOwner,Inv356_R4_1_I1
  \* (Inv356_R4_1_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv356_R4_1_I1 /\ RNodeFailureAction => Inv356_R4_1_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv356_R4_1_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv602_R0_0_I1
THEOREM L_9 == TypeOK /\ Inv29_R0_0_I1 /\ Inv15995_R0_1_I2 /\ Inv602_R0_0_I1 /\ Next => Inv602_R0_0_I1'
  <1>. USE A0,A1
  \* (Inv602_R0_0_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv602_R0_0_I1 /\ RRcvInvAction => Inv602_R0_0_I1' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv29_R0_0_I1 /\ Inv602_R0_0_I1 /\ RRcvValAction => Inv602_R0_0_I1' BY DEF TypeOK,Inv29_R0_0_I1,RRcvValAction,RRcvVal,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RWriteAction)
  <1>3. TypeOK /\ Inv602_R0_0_I1 /\ RWriteAction => Inv602_R0_0_I1' BY DEF TypeOK,RWriteAction,RWrite,Inv602_R0_0_I1,RMessageINV,RMessageVAL
  \* (Inv602_R0_0_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv602_R0_0_I1 /\ RRcvAckAction => Inv602_R0_0_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv15995_R0_1_I2 /\ Inv602_R0_0_I1 /\ RSendValsAction => Inv602_R0_0_I1' BY DEF TypeOK,Inv15995_R0_1_I2,RSendValsAction,RSendVals,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv602_R0_0_I1 /\ RLocalWriteReplayAction => Inv602_R0_0_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv602_R0_0_I1 /\ RFailedNodeWriteReplayAction => Inv602_R0_0_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv602_R0_0_I1 /\ RUpdateLocalEpochIDAction => Inv602_R0_0_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv602_R0_0_I1 /\ ROverthrowOwnerAction => Inv602_R0_0_I1' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv602_R0_0_I1 /\ RNewOwnerAction => Inv602_R0_0_I1' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv602_R0_0_I1
  \* (Inv602_R0_0_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv602_R0_0_I1 /\ RNodeFailureAction => Inv602_R0_0_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv602_R0_0_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv27_R9_1_I1
THEOREM L_10 == TypeOK /\ Inv29_R0_0_I1 /\ Inv15995_R0_1_I2 /\ Inv27_R9_1_I1 /\ Next => Inv27_R9_1_I1'
  <1>. USE A0,A1
  \* (Inv27_R9_1_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv27_R9_1_I1 /\ RRcvInvAction => Inv27_R9_1_I1' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv29_R0_0_I1 /\ Inv27_R9_1_I1 /\ RRcvValAction => Inv27_R9_1_I1' BY DEF TypeOK,Inv29_R0_0_I1,RRcvValAction,RRcvVal,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RWriteAction)
  <1>3. TypeOK /\ Inv27_R9_1_I1 /\ RWriteAction => Inv27_R9_1_I1' BY DEF TypeOK,RWriteAction,RWrite,Inv27_R9_1_I1,RMessageINV,RMessageVAL
  \* (Inv27_R9_1_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv27_R9_1_I1 /\ RRcvAckAction => Inv27_R9_1_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv15995_R0_1_I2 /\ Inv27_R9_1_I1 /\ RSendValsAction => Inv27_R9_1_I1' BY DEF TypeOK,Inv15995_R0_1_I2,RSendValsAction,RSendVals,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv27_R9_1_I1 /\ RLocalWriteReplayAction => Inv27_R9_1_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv27_R9_1_I1 /\ RFailedNodeWriteReplayAction => Inv27_R9_1_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv27_R9_1_I1 /\ RUpdateLocalEpochIDAction => Inv27_R9_1_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv27_R9_1_I1 /\ ROverthrowOwnerAction => Inv27_R9_1_I1' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv27_R9_1_I1 /\ RNewOwnerAction => Inv27_R9_1_I1' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv27_R9_1_I1
  \* (Inv27_R9_1_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv27_R9_1_I1 /\ RNodeFailureAction => Inv27_R9_1_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv27_R9_1_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv234_R4_1_I1
THEOREM L_11 == TypeOK /\ Inv4413_R9_3_I2 /\ Inv12_R4_1_I1 /\ Inv234_R4_1_I1 /\ Next => Inv234_R4_1_I1'
  <1>. USE A0,A1
  \* (Inv234_R4_1_I1,RRcvInvAction)
  <1>1. TypeOK /\ Inv234_R4_1_I1 /\ RRcvInvAction => Inv234_R4_1_I1' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RRcvValAction)
  <1>2. TypeOK /\ Inv234_R4_1_I1 /\ RRcvValAction => Inv234_R4_1_I1' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RWriteAction)
  <1>3. TypeOK /\ Inv4413_R9_3_I2 /\ Inv234_R4_1_I1 /\ RWriteAction => Inv234_R4_1_I1' BY DEF TypeOK,Inv4413_R9_3_I2,RWriteAction,RWrite,Inv234_R4_1_I1,RMessageINV,RMessageVAL
  \* (Inv234_R4_1_I1,RRcvAckAction)
  <1>4. TypeOK /\ Inv234_R4_1_I1 /\ RRcvAckAction => Inv234_R4_1_I1' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RSendValsAction)
  <1>5. TypeOK /\ Inv234_R4_1_I1 /\ RSendValsAction => Inv234_R4_1_I1' BY DEF TypeOK,RSendValsAction,RSendVals,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv234_R4_1_I1 /\ RLocalWriteReplayAction => Inv234_R4_1_I1' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv234_R4_1_I1 /\ RFailedNodeWriteReplayAction => Inv234_R4_1_I1' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv234_R4_1_I1 /\ RUpdateLocalEpochIDAction => Inv234_R4_1_I1' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv234_R4_1_I1 /\ ROverthrowOwnerAction => Inv234_R4_1_I1' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RNewOwnerAction)
  <1>10. TypeOK /\ Inv12_R4_1_I1 /\ Inv234_R4_1_I1 /\ RNewOwnerAction => Inv234_R4_1_I1' BY DEF TypeOK,Inv12_R4_1_I1,RNewOwnerAction,RNewOwner,Inv234_R4_1_I1
  \* (Inv234_R4_1_I1,RNodeFailureAction)
  <1>11. TypeOK /\ Inv234_R4_1_I1 /\ RNodeFailureAction => Inv234_R4_1_I1' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv234_R4_1_I1,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv4413_R9_3_I2
THEOREM L_12 == TypeOK /\ Inv12_R4_1_I1 /\ Inv4413_R9_3_I2 /\ Next => Inv4413_R9_3_I2'
  <1>. USE A0,A1
  \* (Inv4413_R9_3_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv4413_R9_3_I2 /\ RRcvInvAction => Inv4413_R9_3_I2' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv4413_R9_3_I2 /\ RRcvValAction => Inv4413_R9_3_I2' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RWriteAction)
  <1>3. TypeOK /\ Inv4413_R9_3_I2 /\ RWriteAction => Inv4413_R9_3_I2' BY DEF TypeOK,RWriteAction,RWrite,Inv4413_R9_3_I2,RMessageINV,RMessageVAL
  \* (Inv4413_R9_3_I2,RRcvAckAction)
  <1>4. TypeOK /\ Inv4413_R9_3_I2 /\ RRcvAckAction => Inv4413_R9_3_I2' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RSendValsAction)
  <1>5. TypeOK /\ Inv4413_R9_3_I2 /\ RSendValsAction => Inv4413_R9_3_I2' BY DEF TypeOK,RSendValsAction,RSendVals,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv4413_R9_3_I2 /\ RLocalWriteReplayAction => Inv4413_R9_3_I2' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv4413_R9_3_I2 /\ RFailedNodeWriteReplayAction => Inv4413_R9_3_I2' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv4413_R9_3_I2 /\ RUpdateLocalEpochIDAction => Inv4413_R9_3_I2' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv4413_R9_3_I2 /\ ROverthrowOwnerAction => Inv4413_R9_3_I2' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RNewOwnerAction)
  <1>10. TypeOK /\ Inv12_R4_1_I1 /\ Inv4413_R9_3_I2 /\ RNewOwnerAction => Inv4413_R9_3_I2' BY DEF TypeOK,Inv12_R4_1_I1,RNewOwnerAction,RNewOwner,Inv4413_R9_3_I2
  \* (Inv4413_R9_3_I2,RNodeFailureAction)
  <1>11. TypeOK /\ Inv4413_R9_3_I2 /\ RNodeFailureAction => Inv4413_R9_3_I2' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv4413_R9_3_I2,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv82_R9_3_I2
THEOREM L_13 == TypeOK /\ Inv82_R9_3_I2 /\ Next => Inv82_R9_3_I2'
  <1>. USE A0,A1
  \* (Inv82_R9_3_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv82_R9_3_I2 /\ RRcvInvAction => Inv82_R9_3_I2' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv82_R9_3_I2 /\ RRcvValAction => Inv82_R9_3_I2' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RWriteAction)
  <1>3. TypeOK /\ Inv82_R9_3_I2 /\ RWriteAction => Inv82_R9_3_I2' BY DEF TypeOK,RWriteAction,RWrite,Inv82_R9_3_I2,RMessageINV,RMessageVAL
  \* (Inv82_R9_3_I2,RRcvAckAction)
  <1>4. TypeOK /\ Inv82_R9_3_I2 /\ RRcvAckAction => Inv82_R9_3_I2' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RSendValsAction)
  <1>5. TypeOK /\ Inv82_R9_3_I2 /\ RSendValsAction => Inv82_R9_3_I2' BY DEF TypeOK,RSendValsAction,RSendVals,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv82_R9_3_I2 /\ RLocalWriteReplayAction => Inv82_R9_3_I2' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv82_R9_3_I2 /\ RFailedNodeWriteReplayAction => Inv82_R9_3_I2' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv82_R9_3_I2 /\ RUpdateLocalEpochIDAction => Inv82_R9_3_I2' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv82_R9_3_I2 /\ ROverthrowOwnerAction => Inv82_R9_3_I2' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RNewOwnerAction)
  <1>10. TypeOK /\ Inv82_R9_3_I2 /\ RNewOwnerAction => Inv82_R9_3_I2' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv82_R9_3_I2
  \* (Inv82_R9_3_I2,RNodeFailureAction)
  <1>11. TypeOK /\ Inv82_R9_3_I2 /\ RNodeFailureAction => Inv82_R9_3_I2' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv82_R9_3_I2,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv85_R9_3_I2
THEOREM L_14 == TypeOK /\ Inv85_R9_3_I2 /\ Next => Inv85_R9_3_I2'
  <1>. USE A0,A1
  \* (Inv85_R9_3_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv85_R9_3_I2 /\ RRcvInvAction => Inv85_R9_3_I2' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv85_R9_3_I2 /\ RRcvValAction => Inv85_R9_3_I2' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RWriteAction)
  <1>3. TypeOK /\ Inv85_R9_3_I2 /\ RWriteAction => Inv85_R9_3_I2' BY DEF TypeOK,RWriteAction,RWrite,Inv85_R9_3_I2,RMessageINV,RMessageVAL
  \* (Inv85_R9_3_I2,RRcvAckAction)
  <1>4. TypeOK /\ Inv85_R9_3_I2 /\ RRcvAckAction => Inv85_R9_3_I2' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RSendValsAction)
  <1>5. TypeOK /\ Inv85_R9_3_I2 /\ RSendValsAction => Inv85_R9_3_I2' BY DEF TypeOK,RSendValsAction,RSendVals,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv85_R9_3_I2 /\ RLocalWriteReplayAction => Inv85_R9_3_I2' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv85_R9_3_I2 /\ RFailedNodeWriteReplayAction => Inv85_R9_3_I2' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv85_R9_3_I2 /\ RUpdateLocalEpochIDAction => Inv85_R9_3_I2' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv85_R9_3_I2 /\ ROverthrowOwnerAction => Inv85_R9_3_I2' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RNewOwnerAction)
  <1>10. TypeOK /\ Inv85_R9_3_I2 /\ RNewOwnerAction => Inv85_R9_3_I2' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv85_R9_3_I2
  \* (Inv85_R9_3_I2,RNodeFailureAction)
  <1>11. TypeOK /\ Inv85_R9_3_I2 /\ RNodeFailureAction => Inv85_R9_3_I2' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv85_R9_3_I2,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next


\*** Inv407_R0_1_I2
THEOREM L_15 == TypeOK /\ Inv234_R4_1_I1 /\ Inv407_R0_1_I2 /\ Next => Inv407_R0_1_I2'
  <1>. USE A0,A1
  \* (Inv407_R0_1_I2,RRcvInvAction)
  <1>1. TypeOK /\ Inv407_R0_1_I2 /\ RRcvInvAction => Inv407_R0_1_I2' BY DEF TypeOK,RRcvInvAction,RRcvInv,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RRcvValAction)
  <1>2. TypeOK /\ Inv407_R0_1_I2 /\ RRcvValAction => Inv407_R0_1_I2' BY DEF TypeOK,RRcvValAction,RRcvVal,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RWriteAction)
  <1>3. TypeOK /\ Inv234_R4_1_I1 /\ Inv407_R0_1_I2 /\ RWriteAction => Inv407_R0_1_I2' BY DEF TypeOK,Inv234_R4_1_I1,RWriteAction,RWrite,Inv407_R0_1_I2,RMessageINV,RMessageVAL
  \* (Inv407_R0_1_I2,RRcvAckAction)
  <1>4. TypeOK /\ Inv407_R0_1_I2 /\ RRcvAckAction => Inv407_R0_1_I2' BY DEF TypeOK,RRcvAckAction,RRcvAck,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RSendValsAction)
  <1>5. TypeOK /\ Inv407_R0_1_I2 /\ RSendValsAction => Inv407_R0_1_I2' BY DEF TypeOK,RSendValsAction,RSendVals,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RLocalWriteReplayAction)
  <1>6. TypeOK /\ Inv407_R0_1_I2 /\ RLocalWriteReplayAction => Inv407_R0_1_I2' BY DEF TypeOK,RLocalWriteReplayAction,RLocalWriteReplay,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RFailedNodeWriteReplayAction)
  <1>7. TypeOK /\ Inv407_R0_1_I2 /\ RFailedNodeWriteReplayAction => Inv407_R0_1_I2' BY DEF TypeOK,RFailedNodeWriteReplayAction,RFailedNodeWriteReplay,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RUpdateLocalEpochIDAction)
  <1>8. TypeOK /\ Inv407_R0_1_I2 /\ RUpdateLocalEpochIDAction => Inv407_R0_1_I2' BY DEF TypeOK,RUpdateLocalEpochIDAction,RUpdateLocalEpochID,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,ROverthrowOwnerAction)
  <1>9. TypeOK /\ Inv407_R0_1_I2 /\ ROverthrowOwnerAction => Inv407_R0_1_I2' BY DEF TypeOK,ROverthrowOwnerAction,ROverthrowOwner,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RNewOwnerAction)
  <1>10. TypeOK /\ Inv407_R0_1_I2 /\ RNewOwnerAction => Inv407_R0_1_I2' BY DEF TypeOK,RNewOwnerAction,RNewOwner,Inv407_R0_1_I2
  \* (Inv407_R0_1_I2,RNodeFailureAction)
  <1>11. TypeOK /\ Inv407_R0_1_I2 /\ RNodeFailureAction => Inv407_R0_1_I2' BY DEF TypeOK,RNodeFailureAction,RNodeFailure,Inv407_R0_1_I2,RMessageINV,RNoChanges_but_membership
<1>12. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv29_R0_0_I1 BY DEF Init, Inv29_R0_0_I1, IndGlobal
    <1>3. Init => Inv15995_R0_1_I2 BY DEF Init, Inv15995_R0_1_I2, IndGlobal
    <1>4. Init => Inv794_R3_0_I1 BY DEF Init, Inv794_R3_0_I1, IndGlobal
    <1>5. Init => Inv326_R0_1_I2 BY DEF Init, Inv326_R0_1_I2, IndGlobal
    <1>6. Init => Inv30_R4_0_I0 BY DEF Init, Inv30_R4_0_I0, IndGlobal
    <1>7. Init => Inv12_R4_1_I1 BY DEF Init, Inv12_R4_1_I1, IndGlobal
    <1>8. Init => Inv356_R4_1_I1 BY DEF Init, Inv356_R4_1_I1, IndGlobal
    <1>9. Init => Inv602_R0_0_I1 BY DEF Init, Inv602_R0_0_I1, IndGlobal
    <1>10. Init => Inv27_R9_1_I1 BY DEF Init, Inv27_R9_1_I1, IndGlobal
    <1>11. Init => Inv234_R4_1_I1 BY DEF Init, Inv234_R4_1_I1, IndGlobal
    <1>12. Init => Inv4413_R9_3_I2 BY DEF Init, Inv4413_R9_3_I2, IndGlobal
    <1>13. Init => Inv82_R9_3_I2 BY DEF Init, Inv82_R9_3_I2, IndGlobal
    <1>14. Init => Inv85_R9_3_I2 BY DEF Init, Inv85_R9_3_I2, IndGlobal
    <1>15. Init => Inv407_R0_1_I2 BY DEF Init, Inv407_R0_1_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15 DEF Next, IndGlobal

=============================================================================
