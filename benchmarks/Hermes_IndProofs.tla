------------------------------- MODULE Hermes_IndProofs -------------------------------
EXTENDS Hermes, FiniteSetTheorems


\* Proof Graph Stats
\* ==================
\* num proof graph nodes: 6
\* num proof obligations: 60
Safety == HConsistent
Inv45_R0_0_I1 == \A VARI \in aliveNodes : \A VARMVALI \in msgsVAL : ~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker))
Inv532_R0_0_I1 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid"))
Inv4496_R0_1_I2 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] \in {"write", "replay"})) \/ (~(VARI \in nodeRcvedAcks[VARJ]))
Inv3754_R3_0_I1 == \A VARI \in aliveNodes : (nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] \in {"write", "replay"}))
Inv5300_R3_0_I1 == \A VARI \in aliveNodes : \A VARMACKI \in msgsACK : ~(VARMACKI.sender = VARI) \/ (~(greaterTS(VARMACKI.version, VARMACKI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv45_R0_0_I1
  /\ Inv4496_R0_1_I2
  /\ Inv3754_R3_0_I1
  /\ Inv5300_R3_0_I1
  /\ Inv532_R0_0_I1


\* mean in-degree: 0.8333333333333334
\* median in-degree: 1
\* max in-degree: 2
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME Fin == IsFiniteSet(H_NODES) /\ H_NODES \subseteq Nat

\* Optional finitization.
ASSUME NFIN == H_NODES = {0,1,2,3,4}
USE NFIN

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,HRcvInvAction)
  <1>1. TypeOK /\ TypeOK /\ HRcvInvAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HRcvInvAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \in INVMessage)'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>2. (msgsVAL \in VALMessage)'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>3. (msgsACK \in ACKMessage)'
      <3> SUFFICES ASSUME NEW n \in aliveNodes, NEW m \in msgsINV,
                          HRcvInv(n, m)
                   PROVE  (msgsACK \in ACKMessage)'
        BY DEF HRcvInvAction
      <3> QED
        BY Fin,FS_CardinalityType ,FS_Subset,FS_EmptySet,FS_Singleton DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK,ACKMessage,INVMessage,greaterTS
      
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : 0..H_MAX_VERSION, tieBreaker: H_NODES ]])'
      BY Fin DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : 0..H_MAX_VERSION, tieBreaker: H_NODES ]])'
      BY Fin DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>11. (epochID         \in 0..(Cardinality(H_NODES) - 1))'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)])'
      BY DEF TypeOK,HRcvInvAction,HRcvInv,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
  \* (TypeOK,HRcvInvNewerAction)
  <1>2. TypeOK /\ TypeOK /\ HRcvInvNewerAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HRcvInvNewerAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \in INVMessage)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>2. (msgsVAL \in VALMessage)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>3. (msgsACK \in ACKMessage)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>11. (epochID         \in 0..(Cardinality(H_NODES) - 1))'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)])'
      BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
  \* (TypeOK,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ TypeOK /\ HFollowerWriteReplayAction => TypeOK'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,TypeOK
  \* (TypeOK,HRcvValAction)
  <1>4. TypeOK /\ TypeOK /\ HRcvValAction => TypeOK'
       BY DEF TypeOK,HRcvValAction,HRcvVal,TypeOK
  \* (TypeOK,HReadAction)
  <1>5. TypeOK /\ TypeOK /\ HReadAction => TypeOK'
       BY DEF TypeOK,HReadAction,HRead,TypeOK,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes
  \* (TypeOK,HCoordWriteReplayAction)
  <1>6. TypeOK /\ TypeOK /\ HCoordWriteReplayAction => TypeOK'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,TypeOK
  \* (TypeOK,HWriteAction)
  <1>7. TypeOK /\ TypeOK /\ HWriteAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HWriteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \in INVMessage)'
      BY Fin DEF TypeOK,HWriteAction,HWrite,TypeOK,INVMessage
    <2>2. (msgsVAL \in VALMessage)'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>3. (msgsACK \in ACKMessage)'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>11. (epochID         \in 0..(Cardinality(H_NODES) - 1))'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)])'
      BY DEF TypeOK,HWriteAction,HWrite,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
  \* (TypeOK,HRcvAckAction)
  <1>8. TypeOK /\ TypeOK /\ HRcvAckAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HRcvAckAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \in INVMessage)'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>2. (msgsVAL \in VALMessage)'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>3. (msgsACK \in ACKMessage)'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY Fin, FS_SUBSET,FS_Singleton,FS_Subset DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK,ACKMessage,equalTS
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      <3> SUFFICES ASSUME NEW n \in H_NODES'
                   PROVE  (nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
        OBVIOUS
      <3> QED
        BY Fin, FS_SUBSET,FS_Singleton,FS_Subset DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK,ACKMessage,equalTS
      
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>11. (epochID         \in 0..(Cardinality(H_NODES) - 1))'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)])'
      BY DEF TypeOK,HRcvAckAction,HRcvAck,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
  \* (TypeOK,HSendValsAction)
  <1>9. TypeOK /\ TypeOK /\ HSendValsAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HSendValsAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \in INVMessage)'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>2. (msgsVAL \in VALMessage)'
      BY Fin DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>3. (msgsACK \in ACKMessage)'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>11. (epochID         \in 0..(Cardinality(H_NODES) - 1))'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>12. (nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)])'
      BY DEF TypeOK,HSendValsAction,HSendVals,TypeOK,receivedAllAcks,VALMessage
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
  \* (TypeOK,NodeFailureAction)
  <1>10. TypeOK /\ TypeOK /\ NodeFailureAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ NodeFailureAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (msgsINV \in INVMessage)'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>2. (msgsVAL \in VALMessage)'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>3. (msgsACK \in ACKMessage)'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>4. (nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES])'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>5. (\A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n}))'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>6. (nodeLastWriter  \in [H_NODES -> H_NODES])'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>7. (nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>8. (nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]])'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>9. (nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}])'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>10. (aliveNodes      \in SUBSET H_NODES)'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>11. (epochID         \in 0..(Cardinality(H_NODES) - 1))'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>12. (nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)])'
      BY DEF TypeOK,NodeFailureAction,NodeFailure,TypeOK
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
       
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next



\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv45_R0_0_I1 /\ Inv532_R0_0_I1 /\ Safety /\ Next => Safety'
  \* (Safety,HRcvInvAction)
  <1>1. TypeOK /\ Safety /\ HRcvInvAction => Safety'
       BY DEF TypeOK,HRcvInvAction,HRcvInv,Safety,HConsistent
  \* (Safety,HRcvInvNewerAction)
  <1>2. TypeOK /\ Safety /\ HRcvInvNewerAction => Safety'
       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Safety,HConsistent
  \* (Safety,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Safety /\ HFollowerWriteReplayAction => Safety'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Safety,HConsistent
  \* (Safety,HRcvValAction)
  <1>4. TypeOK /\ Inv45_R0_0_I1 /\ Inv532_R0_0_I1 /\ Safety /\ HRcvValAction => Safety'
       BY DEF TypeOK,Inv45_R0_0_I1,Inv532_R0_0_I1,HRcvValAction,HRcvVal,Safety,HConsistent,equalTS,greaterOrEqualTS,greaterTS,VALMessage
  \* (Safety,HReadAction)
  <1>5. TypeOK /\ Safety /\ HReadAction => Safety'
       BY DEF TypeOK,HReadAction,HRead,Safety,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes,HConsistent
  \* (Safety,HCoordWriteReplayAction)
  <1>6. TypeOK /\ Safety /\ HCoordWriteReplayAction => Safety'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Safety,HConsistent
  \* (Safety,HWriteAction)
  <1>7. TypeOK /\ Safety /\ HWriteAction => Safety'
       BY DEF TypeOK,HWriteAction,HWrite,Safety,HConsistent
  \* (Safety,HRcvAckAction)
  <1>8. TypeOK /\ Safety /\ HRcvAckAction => Safety'
       BY DEF TypeOK,HRcvAckAction,HRcvAck,Safety,HConsistent
  \* (Safety,HSendValsAction)
  <1>9. TypeOK /\ Safety /\ HSendValsAction => Safety'
       BY DEF TypeOK,HSendValsAction,HSendVals,Safety,receivedAllAcks,VALMessage,HConsistent
  \* (Safety,NodeFailureAction)
  <1>10. TypeOK /\ Safety /\ NodeFailureAction => Safety'
       BY DEF TypeOK,NodeFailureAction,NodeFailure,Safety,HConsistent
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next


\*** Inv45_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv4496_R0_1_I2 /\ Inv45_R0_0_I1 /\ Next => Inv45_R0_0_I1'
  \* (Inv45_R0_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv45_R0_0_I1 /\ HRcvInvAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv45_R0_0_I1 /\ HRcvInvNewerAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv45_R0_0_I1 /\ HFollowerWriteReplayAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv45_R0_0_I1 /\ HRcvValAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HRcvValAction,HRcvVal,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HReadAction)
  <1>5. TypeOK /\ Inv45_R0_0_I1 /\ HReadAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HReadAction,HRead,Inv45_R0_0_I1,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes
  \* (Inv45_R0_0_I1,HCoordWriteReplayAction)
  <1>6. TypeOK /\ Inv45_R0_0_I1 /\ HCoordWriteReplayAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HWriteAction)
  <1>7. TypeOK /\ Inv45_R0_0_I1 /\ HWriteAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HWriteAction,HWrite,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HRcvAckAction)
  <1>8. TypeOK /\ Inv45_R0_0_I1 /\ HRcvAckAction => Inv45_R0_0_I1'
       BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv45_R0_0_I1
  \* (Inv45_R0_0_I1,HSendValsAction)
  <1>9. TypeOK /\ Inv4496_R0_1_I2 /\ Inv45_R0_0_I1 /\ HSendValsAction => Inv45_R0_0_I1'
       BY DEF TypeOK,Inv4496_R0_1_I2,HSendValsAction,HSendVals,Inv45_R0_0_I1,receivedAllAcks,VALMessage
  \* (Inv45_R0_0_I1,NodeFailureAction)
  <1>10. TypeOK /\ Inv45_R0_0_I1 /\ NodeFailureAction => Inv45_R0_0_I1'
       BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv45_R0_0_I1
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next


\*** Inv4496_R0_1_I2
THEOREM L_3 == TypeOK /\ Inv3754_R3_0_I1 /\ Inv5300_R3_0_I1 /\ Inv4496_R0_1_I2 /\ Next => Inv4496_R0_1_I2'
  \* (Inv4496_R0_1_I2,HRcvInvAction)
  <1>1. TypeOK /\ Inv4496_R0_1_I2 /\ HRcvInvAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv4496_R0_1_I2 /\ HRcvInvNewerAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv4496_R0_1_I2 /\ HFollowerWriteReplayAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HRcvValAction)
  <1>4. TypeOK /\ Inv4496_R0_1_I2 /\ HRcvValAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HRcvValAction,HRcvVal,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HReadAction)
  <1>5. TypeOK /\ Inv4496_R0_1_I2 /\ HReadAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HReadAction,HRead,Inv4496_R0_1_I2,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes
  \* (Inv4496_R0_1_I2,HCoordWriteReplayAction)
  <1>6. TypeOK /\ Inv4496_R0_1_I2 /\ HCoordWriteReplayAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HWriteAction)
  <1>7. TypeOK /\ Inv4496_R0_1_I2 /\ HWriteAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HWriteAction,HWrite,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HRcvAckAction)
  <1>8. TypeOK /\ Inv3754_R3_0_I1 /\ Inv5300_R3_0_I1 /\ Inv4496_R0_1_I2 /\ HRcvAckAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,Inv3754_R3_0_I1,Inv5300_R3_0_I1,HRcvAckAction,HRcvAck,Inv4496_R0_1_I2
  \* (Inv4496_R0_1_I2,HSendValsAction)
  <1>9. TypeOK /\ Inv4496_R0_1_I2 /\ HSendValsAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,HSendValsAction,HSendVals,Inv4496_R0_1_I2,receivedAllAcks,VALMessage
  \* (Inv4496_R0_1_I2,NodeFailureAction)
  <1>10. TypeOK /\ Inv4496_R0_1_I2 /\ NodeFailureAction => Inv4496_R0_1_I2'
       BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv4496_R0_1_I2
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next


\*** Inv3754_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv3754_R3_0_I1 /\ Next => Inv3754_R3_0_I1'
  \* (Inv3754_R3_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv3754_R3_0_I1 /\ HRcvInvAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv3754_R3_0_I1 /\ HRcvInvNewerAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv3754_R3_0_I1 /\ HFollowerWriteReplayAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv3754_R3_0_I1 /\ HRcvValAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HRcvValAction,HRcvVal,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HReadAction)
  <1>5. TypeOK /\ Inv3754_R3_0_I1 /\ HReadAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HReadAction,HRead,Inv3754_R3_0_I1,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes
  \* (Inv3754_R3_0_I1,HCoordWriteReplayAction)
  <1>6. TypeOK /\ Inv3754_R3_0_I1 /\ HCoordWriteReplayAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HWriteAction)
  <1>7. TypeOK /\ Inv3754_R3_0_I1 /\ HWriteAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HWriteAction,HWrite,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HRcvAckAction)
  <1>8. TypeOK /\ Inv3754_R3_0_I1 /\ HRcvAckAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv3754_R3_0_I1
  \* (Inv3754_R3_0_I1,HSendValsAction)
  <1>9. TypeOK /\ Inv3754_R3_0_I1 /\ HSendValsAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,HSendValsAction,HSendVals,Inv3754_R3_0_I1,receivedAllAcks,VALMessage
  \* (Inv3754_R3_0_I1,NodeFailureAction)
  <1>10. TypeOK /\ Inv3754_R3_0_I1 /\ NodeFailureAction => Inv3754_R3_0_I1'
       BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv3754_R3_0_I1
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next


\*** Inv5300_R3_0_I1
THEOREM L_5 == TypeOK /\ Inv5300_R3_0_I1 /\ Next => Inv5300_R3_0_I1'
  \* (Inv5300_R3_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv5300_R3_0_I1 /\ HRcvInvAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv5300_R3_0_I1
  \* (Inv5300_R3_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv5300_R3_0_I1 /\ HRcvInvNewerAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv5300_R3_0_I1
  \* (Inv5300_R3_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv5300_R3_0_I1 /\ HFollowerWriteReplayAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv5300_R3_0_I1
  \* (Inv5300_R3_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv5300_R3_0_I1 /\ HRcvValAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HRcvValAction,HRcvVal,Inv5300_R3_0_I1
  \* (Inv5300_R3_0_I1,HReadAction)
  <1>5. TypeOK /\ Inv5300_R3_0_I1 /\ HReadAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HReadAction,HRead,Inv5300_R3_0_I1,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes
  \* (Inv5300_R3_0_I1,HCoordWriteReplayAction)
  <1>6. TypeOK /\ Inv5300_R3_0_I1 /\ HCoordWriteReplayAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv5300_R3_0_I1
  \* (Inv5300_R3_0_I1,HWriteAction)
  <1>7. TypeOK /\ Inv5300_R3_0_I1 /\ HWriteAction => Inv5300_R3_0_I1'
    <2> SUFFICES ASSUME TypeOK /\ Inv5300_R3_0_I1 /\ HWriteAction,
                        NEW VARI \in aliveNodes',
                        NEW VARMACKI \in msgsACK'
                 PROVE  (~(VARMACKI.sender = VARI) \/ (~(greaterTS(VARMACKI.version, VARMACKI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker))))'
      BY DEF Inv5300_R3_0_I1
    <2>     QED
      BY Fin DEF TypeOK,HWriteAction,HWrite,Inv5300_R3_0_I1,greaterTS,ACKMessage,INVMessage, VALMessage
       
  \* (Inv5300_R3_0_I1,HRcvAckAction)
  <1>8. TypeOK /\ Inv5300_R3_0_I1 /\ HRcvAckAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv5300_R3_0_I1
  \* (Inv5300_R3_0_I1,HSendValsAction)
  <1>9. TypeOK /\ Inv5300_R3_0_I1 /\ HSendValsAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,HSendValsAction,HSendVals,Inv5300_R3_0_I1,receivedAllAcks,VALMessage
  \* (Inv5300_R3_0_I1,NodeFailureAction)
  <1>10. TypeOK /\ Inv5300_R3_0_I1 /\ NodeFailureAction => Inv5300_R3_0_I1'
       BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv5300_R3_0_I1
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next


\*** Inv532_R0_0_I1
THEOREM L_6 == TypeOK /\ Inv532_R0_0_I1 /\ Next => Inv532_R0_0_I1'
  \* (Inv532_R0_0_I1,HRcvInvAction)
  <1>1. TypeOK /\ Inv532_R0_0_I1 /\ HRcvInvAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HRcvInvAction,HRcvInv,Inv532_R0_0_I1
  \* (Inv532_R0_0_I1,HRcvInvNewerAction)
  <1>2. TypeOK /\ Inv532_R0_0_I1 /\ HRcvInvNewerAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HRcvInvNewerAction,HRcvInvNewer,Inv532_R0_0_I1,greaterOrEqualTS,greaterTS,equalTS
  \* (Inv532_R0_0_I1,HFollowerWriteReplayAction)
  <1>3. TypeOK /\ Inv532_R0_0_I1 /\ HFollowerWriteReplayAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HFollowerWriteReplayAction,HFollowerWriteReplay,Inv532_R0_0_I1
  \* (Inv532_R0_0_I1,HRcvValAction)
  <1>4. TypeOK /\ Inv532_R0_0_I1 /\ HRcvValAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HRcvValAction,HRcvVal,Inv532_R0_0_I1
  \* (Inv532_R0_0_I1,HReadAction)
  <1>5. TypeOK /\ Inv532_R0_0_I1 /\ HReadAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HReadAction,HRead,Inv532_R0_0_I1,h_upd_nothing,h_upd_not_aliveNodes,h_upd_aliveNodes
  \* (Inv532_R0_0_I1,HCoordWriteReplayAction)
  <1>6. TypeOK /\ Inv532_R0_0_I1 /\ HCoordWriteReplayAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HCoordWriteReplayAction,HCoordWriteReplay,Inv532_R0_0_I1
  \* (Inv532_R0_0_I1,HWriteAction)
  <1>7. TypeOK /\ Inv532_R0_0_I1 /\ HWriteAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HWriteAction,HWrite,Inv532_R0_0_I1,greaterOrEqualTS,greaterTS,equalTS
  \* (Inv532_R0_0_I1,HRcvAckAction)
  <1>8. TypeOK /\ Inv532_R0_0_I1 /\ HRcvAckAction => Inv532_R0_0_I1'
       BY DEF TypeOK,HRcvAckAction,HRcvAck,Inv532_R0_0_I1
  \* (Inv532_R0_0_I1,HSendValsAction)
  <1>9. TypeOK /\ Inv532_R0_0_I1 /\ HSendValsAction => Inv532_R0_0_I1'
       BY Fin,FS_CardinalityType ,FS_Subset,FS_Difference,FS_SUBSET,FS_EmptySet,FS_Singleton DEF TypeOK,HSendValsAction,HSendVals,Inv532_R0_0_I1,receivedAllAcks,VALMessage,greaterOrEqualTS,greaterTS,equalTS
  \* (Inv532_R0_0_I1,NodeFailureAction)
  <1>10. TypeOK /\ Inv532_R0_0_I1 /\ NodeFailureAction => Inv532_R0_0_I1'
       BY DEF TypeOK,NodeFailureAction,NodeFailure,Inv532_R0_0_I1
<1>11. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6 DEF Next, IndGlobal



=============================================================================
