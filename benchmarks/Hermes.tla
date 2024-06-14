------------------------------- MODULE Hermes -------------------------------
\* 
\* Spec source: https://github.com/ease-lab/Hermes
\* 

EXTENDS     Integers,
            FiniteSets

CONSTANTS   H_NODES,
            H_MAX_VERSION
            
VARIABLES   msgsINV,
            msgsVAL,
            msgsACK,
            nodeTS,
            nodeState, 
            nodeRcvedAcks,
            nodeLastWriter,
            nodeLastWriteTS,
            nodeWriteEpochID, 
            aliveNodes,
            epochID 
            
\* all Hermes (+ environment) variables
hvars == << msgsINV, msgsVAL, msgsACK, nodeTS, nodeState, nodeRcvedAcks, nodeLastWriter, 
            nodeLastWriteTS, nodeWriteEpochID, aliveNodes, epochID >>

-------------------------------------------------------------------------------------

\* Invalidation (INV) messages are broadcast when a write comes in that
\* cannot be completed due to a node not currently being in a valid state.
INVMessage == [
    type: {"INV"}, 
    sender    : H_NODES,
    epochID   : Nat,
    version   : Nat,  
    tieBreaker: H_NODES
] 

\* Acknowledgment (ACK) messages are sent by nodes back to 
\* the coordinator to acknowledge the receipt of an INV message.
\* Once the coordinator receives ACKS from all live replicas, the 
\* write is completed by transitioning the key to the Valid state.
ACKMessage == [
    type: {"ACK"}, 
    sender    : H_NODES,
    epochID   : Nat,
    version   : Nat,  
    tieBreaker: H_NODES
]

\* After receipt of enough ACK messages, a coordinator will broadcast a VAL
\* message with the key and the same timestamp to all followers.
VALMessage == [
    type: {"VAL"},        \* optimization: epochID is not required for VALs
                          \* epochID   : 0..(Cardinality(H_NODES) - 1),
    version   : Nat, 
    tieBreaker: H_NODES    
]

Message ==  INVMessage \cup ACKMessage \cup VALMessage

TypeOK ==  \* The type correctness invariant
    /\ msgsINV \subseteq INVMessage
    /\ msgsVAL \subseteq VALMessage
    /\ msgsACK \subseteq ACKMessage
    /\ nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES]
    /\ \A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n})
    /\  nodeLastWriter  \in [H_NODES -> H_NODES]
    /\  nodeLastWriteTS \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]]
    /\  nodeTS          \in [H_NODES -> [version : Nat, tieBreaker: H_NODES ]]
    /\  nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}]
    \*  membership and epoch id related
    /\  aliveNodes      \in SUBSET H_NODES
    /\  epochID         \in Nat
    /\  nodeWriteEpochID \in [H_NODES -> Nat]

Init == \* The initial predicate
    /\  msgsINV            = {}
    /\  msgsVAL            = {}
    /\  msgsACK            = {}
    \*  membership and epoch id related
    /\  epochID         = 0
    /\  aliveNodes      = H_NODES
    /\  nodeWriteEpochID = [n \in H_NODES |-> 0]
    \*  Init rest per node replica metadata
    /\  nodeRcvedAcks   = [n \in H_NODES |-> {}]
    /\  nodeState       = [n \in H_NODES |-> "valid"]
    /\  nodeLastWriter  = [n \in H_NODES |-> CHOOSE k \in H_NODES:
                                             \A m \in H_NODES: k <= m]
    /\  nodeTS          = [n \in H_NODES |-> [version |-> 0, 
                                              tieBreaker |-> 
                                              CHOOSE k \in H_NODES: 
                                               \A m \in H_NODES: k <= m]]
    /\  nodeLastWriteTS = [n \in H_NODES |-> [version |-> 0, 
                                              tieBreaker |-> 
                                              CHOOSE k \in H_NODES: 
                                               \A m \in H_NODES: k <= m]]
                                               
-------------------------------------------------------------------------------------

\* A buffer maintaining all network messages. Messages are only appended to this variable (not 
\* removed once delivered) intentionally to check protocols tolerance in dublicates and reorderings 
send(m, msgs) == msgs' = msgs \union {m}

\* Check if all acknowledgments for a write have been received                                                  
\*receivedAllAcks(n) == nodeRcvedAcks[n] = H_NODES \ {n}
receivedAllAcks(n) == (aliveNodes \ {n}) \subseteq nodeRcvedAcks[n]
        
equalTS(v1,tb1,v2,tb2) ==  \* Timestamp equality
    /\ v1 = v2
    /\ tb1 = tb2

greaterTS(v1,tb1,v2,tb2) == \* Timestamp comparison
    \/ v1 > v2
    \/ /\   v1 = v2
       /\  tb1 > tb2

greaterOrEqualTS(v1,tb1,v2,tb2) == 
    \/ equalTS(v1,tb1,v2,tb2)
    \/ greaterTS(v1,tb1,v2,tb2)       

isAlive(n) == n \in aliveNodes
                   
NodeFailure(n) == \* Emulate a node failure
    \* Make sure that there are atleast 3 alive nodes before killing a node
    /\ Cardinality(aliveNodes) > 2
    /\ nodeRcvedAcks' = [k \in H_NODES |-> {}]
    /\ aliveNodes'    = aliveNodes \ {n}
    /\ epochID'       = epochID + 1
    /\ UNCHANGED <<msgsINV, msgsACK, msgsVAL, nodeState, nodeTS, nodeLastWriter, nodeLastWriteTS, nodeWriteEpochID>>

h_upd_not_aliveNodes ==
    /\  UNCHANGED <<aliveNodes, epochID, nodeWriteEpochID>>
    
    
h_upd_aliveNodes ==
    /\ UNCHANGED <<msgsINV, msgsACK, msgsVAL, nodeState, nodeTS, nodeLastWriter, nodeLastWriteTS, nodeRcvedAcks>>
                   
h_upd_nothing ==                    
    /\ h_upd_not_aliveNodes
    /\ h_upd_aliveNodes
    
-------------------------------------------------------------------------------------

h_upd_state(n, newVersion, newTieBreaker, newState, newAcks) == 
    /\  nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\  nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = newAcks]
    /\  nodeState'        = [nodeState       EXCEPT ![n] = newState]
    /\  nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID] \* we always use the latest epochID
    /\  nodeTS'           = [nodeTS          EXCEPT ![n].version    = newVersion, 
                                                    ![n].tieBreaker = newTieBreaker]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version    = newVersion, 
                                                    ![n].tieBreaker = newTieBreaker]
                                            
h_send_inv_or_ack(n, newVersion, newTieBreaker, msgType, msgs) ==  
    /\  send([type        |-> msgType,
              epochID     |-> epochID, \* we always use the latest epochID
              sender      |-> n,
              version     |-> newVersion, 
              tieBreaker  |-> newTieBreaker], msgs)              

h_actions_for_upd(n, newVersion, newTieBreaker, newState, newAcks) == \* Execute a write
    /\  h_upd_state(n, newVersion, newTieBreaker, newState, newAcks)
    /\  h_send_inv_or_ack(n, newVersion, newTieBreaker, "INV", msgsINV)
    /\  UNCHANGED <<aliveNodes, epochID, msgsVAL, msgsACK>>
 

h_actions_for_upd_replay(n, acks) == \* Apply a write-replay using same TS (version, tie-breaker) 
                                     \* and either reset acks or keep already gathered acks
    /\  h_actions_for_upd(n, nodeTS[n].version, nodeTS[n].tieBreaker, "replay", acks)

-------------------------------------------------------------------------------------

HRead(n) ==  \* Execute a read
    /\ nodeState[n] = "valid"
    /\ h_upd_nothing
              
HWrite(n) == \* Execute a write
    \* writes in invalid state are also supported as an optimization
    /\  n \in aliveNodes
    /\  nodeState[n]      \in {"valid"}
    /\  nodeTS[n].version < H_MAX_VERSION \* Only to configurably terminate the model checking 
    /\  nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\  nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = {}]
    /\  nodeState'        = [nodeState       EXCEPT ![n] = "write"]
    /\  nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID] \* we always use the latest epochID
    /\  nodeTS'           = [nodeTS          EXCEPT ![n].version    = nodeTS[n].version + 1, 
                                                    ![n].tieBreaker = n]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version    = nodeTS[n].version + 1, 
                                                    ![n].tieBreaker = n]
    \* /\  h_send_inv_or_ack(n, nodeTS[n].version + 1, n, "INV", msgsINV)
    /\ msgsINV' = msgsINV \cup {
        [type        |-> "INV",
              epochID     |-> epochID, \* we always use the latest epochID
              sender      |-> n,
              version     |-> nodeTS[n].version + 1, 
              tieBreaker  |-> n]}
    /\  UNCHANGED <<aliveNodes, epochID, msgsVAL, msgsACK>>

HCoordWriteReplay(n) == \* Execute a write-replay after a membership re-config
    /\ n \in aliveNodes
    /\  nodeState[n] \in {"write", "replay"}
    /\  nodeWriteEpochID[n] < epochID
    /\  ~receivedAllAcks(n) \* optimization to not replay when we have gathered acks from all alive
    /\ nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\ nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = nodeRcvedAcks[n]]
    /\ nodeState'        = [nodeState       EXCEPT ![n] = "replay"]
    /\ nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID] \* we always use the latest epochID
    /\ nodeTS'           = [nodeTS          EXCEPT ![n].version    = nodeTS[n].version, 
                                                   ![n].tieBreaker = nodeTS[n].tieBreaker]
    /\ nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version    = nodeTS[n].version, 
                                                    ![n].tieBreaker = nodeTS[n].tieBreaker]
    /\ msgsINV' = msgsINV \cup {[type        |-> "INV",
                                 epochID     |-> epochID, \* we always use the latest epochID
                                 sender      |-> n,
                                 version     |-> nodeTS[n].version, 
                                 tieBreaker  |-> nodeTS[n].tieBreaker]}
    /\  UNCHANGED <<aliveNodes, epochID, msgsVAL, msgsACK>>

HRcvAck(n, m) ==   \* Process a received acknowledment
    /\ n \in aliveNodes
    /\ m \in msgsACK
    /\ m.type     = "ACK"
    /\ m.epochID  = epochID
    /\ m.sender  /= n
    /\ m.sender  \notin nodeRcvedAcks[n]
    /\ equalTS(m.version, m.tieBreaker,
                nodeLastWriteTS[n].version, 
                nodeLastWriteTS[n].tieBreaker)
    /\ nodeState[n] \in {"write", "invalid_write", "replay"}
    /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = nodeRcvedAcks[n] \union {m.sender}]
    /\ UNCHANGED <<msgsINV, msgsACK, msgsVAL, nodeLastWriter, nodeLastWriteTS, aliveNodes, nodeTS, nodeState, epochID, nodeWriteEpochID>>


HSendVals(n) == \* Send validations once acknowledments are received from all alive nodes
    /\ nodeState[n] \in {"write", "replay"}
    /\ n \in aliveNodes
    /\ receivedAllAcks(n)
    /\ nodeState'         = [nodeState EXCEPT![n] = "valid"]
    /\ msgsVAL' = msgsVAL \cup {([type        |-> "VAL", 
                            version     |-> nodeTS[n].version, 
                            tieBreaker  |-> nodeTS[n].tieBreaker])}
    /\ UNCHANGED <<nodeTS, nodeLastWriter, nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsACK, msgsINV>>
 
HCoordinatorActions(n) ==   \* Actions of a read/write coordinator 
    \/ HRead(n)          
    \/ HCoordWriteReplay(n) \* After failures
    \/ HWrite(n)         
    \* \/ HRcvAck(n)
    \/ HSendVals(n) 

-------------------------------------------------------------------------------------               

HRcvInvNewer(n, m) ==  \* Process a received invalidation
    /\ n \in aliveNodes
    /\ m \in msgsINV 
    /\ m.type     = "INV"
    /\ m.epochID  = epochID
    /\ m.sender  # n
    \* always acknowledge a received invalidation (irrelevant to the timestamp)
    /\ msgsACK' = msgsACK \cup {[type       |-> "ACK",
                                 sender     |-> n,   
                                 epochID    |-> epochID,
                                 version    |-> m.version,
                                 tieBreaker |-> m.tieBreaker]}
    /\ greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
    /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
    /\ nodeTS' = [nodeTS EXCEPT ![n].version    = m.version, ![n].tieBreaker = m.tieBreaker]
    /\ IF nodeState[n] \in {"valid", "invalid", "replay"}
            THEN 
            nodeState' = [nodeState EXCEPT ![n] = "invalid"]
            ELSE 
            nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
    /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV>>
 
HRcvInv(n, m) ==  \* Process a received invalidation
    /\ n \in aliveNodes
    /\ m \in msgsINV 
    /\ m.type     = "INV"
    /\ m.epochID  = epochID
    /\ m.sender  # n
    \* always acknowledge a received invalidation (irrelevant to the timestamp)
    /\ msgsACK' = msgsACK \cup {[type       |-> "ACK",
                                 sender     |-> n,   
                                 epochID    |-> epochID,
                                 version    |-> m.version,
                                 tieBreaker |-> m.tieBreaker]}
    /\ ~greaterTS(m.version, m.tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)
    /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID, msgsVAL, msgsINV, nodeState, nodeTS, nodeLastWriter, nodeWriteEpochID>>
     
HRcvVal(n, m) ==   \* Process a received validation
    /\ m \in msgsVAL
    /\ n \in aliveNodes
    /\ nodeState[n] /= "valid"
    /\ m.type = "VAL"
    /\ equalTS(m.version, m.tieBreaker,
                nodeTS[n].version, 
                nodeTS[n].tieBreaker)
    /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
    /\ UNCHANGED <<msgsINV, msgsACK, msgsVAL, nodeTS, nodeLastWriter, nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>

HFollowerWriteReplay(n) == \* Execute a write-replay when coordinator failed
    /\  nodeState[n] \in {"invalid", "invalid_write"}
    /\  ~isAlive(nodeLastWriter[n])
    /\ nodeLastWriter'   = [nodeLastWriter  EXCEPT ![n] = n]
    /\ nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = {}]
    /\ nodeState'        = [nodeState       EXCEPT ![n] = "replay"]
    /\ nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID] \* we always use the latest epochID
    /\ nodeTS'           = [nodeTS          EXCEPT ![n].version    = nodeTS[n].version, 
                                                   ![n].tieBreaker = nodeTS[n].tieBreaker]
    /\ nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version    = nodeTS[n].version, 
                                                    ![n].tieBreaker = nodeTS[n].tieBreaker]
    /\ msgsINV' = msgsINV \cup {[type        |-> "INV",
                                 epochID     |-> epochID, \* we always use the latest epochID
                                 sender      |-> n,
                                 version     |-> nodeTS[n].version, 
                                 tieBreaker  |-> nodeTS[n].tieBreaker]}
    /\  UNCHANGED <<aliveNodes, epochID, msgsVAL, msgsACK>>
   
HFollowerActions(n, m) ==  \* Actions of a write follower
    \/ HRcvInv(n, m)
    \/ HFollowerWriteReplay(n)
    \/ HRcvVal(n, m) 
 
------------------------------------------------------------------------------------- 

HRcvInvAction == TRUE /\ \E n \in aliveNodes, m \in msgsINV : HRcvInv(n, m)
HRcvInvNewerAction == TRUE /\ \E n \in aliveNodes, m \in msgsINV : HRcvInvNewer(n, m)
HFollowerWriteReplayAction == TRUE /\ \E n \in aliveNodes : HFollowerWriteReplay(n)
HRcvValAction == TRUE /\ \E n \in aliveNodes, m \in msgsVAL : HRcvVal(n, m)
\* HReadAction == TRUE /\ \E n \in aliveNodes : HRead(n)
HCoordWriteReplayAction == TRUE /\ \E n \in aliveNodes : HCoordWriteReplay(n)
HWriteAction == TRUE /\ \E n \in aliveNodes : HWrite(n)
HRcvAckAction == TRUE /\ \E n \in aliveNodes, m \in msgsACK : HRcvAck(n, m)
HSendValsAction == TRUE /\ \E n \in aliveNodes : HSendVals(n)
NodeFailureAction == TRUE /\ \E n \in aliveNodes : NodeFailure(n)

Next == \* Hermes (read/write) protocol (Coordinator and Follower actions) + failures
    \* Follower actions.
    \/ HRcvInvAction
    \/ HRcvInvNewerAction
    \/ HFollowerWriteReplayAction
    \/ HRcvValAction
    \* Coordinator actions (leader of writes/reads)
    \* \/ HReadAction
    \/ HCoordWriteReplayAction
    \/ HWriteAction
    \/ HRcvAckAction
    \/ HSendValsAction
    \* Failure actions.
    \/ NodeFailureAction


Spec == Init /\ [][Next]_hvars


\* The consistent invariant: all alive nodes in valid state should have the same value / TS         
HConsistent == 
    \A k,s \in aliveNodes:  
        (nodeState[k] = "valid" /\ nodeState[s] = "valid") => nodeTS[k] = nodeTS[s]



\* THEOREM H_Spec =>([]HTypeOK) /\ ([]HConsistent)

NextUnchanged == UNCHANGED hvars

VALMsgs == msgsVAL


Alias == [
    nodeTS |-> nodeTS,
    msgs |-> msgsVAL,
    nodeState |-> nodeState,
    aliveNodes  |-> aliveNodes
]

Alias2 == [
    aliveNodes |-> aliveNodes,
    \* msgs |-> VALMsgs,
    nodeRcvedAcks |-> nodeRcvedAcks,
    nodeState |-> nodeState,
    nodeTS |-> nodeTS
]

T1 == \A VARI \in H_NODES : \A VARJ \in H_NODES : nodeTS = nodeTS /\ msgsVAL = msgsVAL


\* 
\* Lemmas for inductive invariant.
\* 

H_Inv18_1_0 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (VARI \in aliveNodes) \/ (~(nodeState[VARI] = "replay"))
H_Inv2558_2_1 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(VARI \in aliveNodes)) \/ (~(nodeState[VARJ] = "valid"))
H_Inv2587_2_2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARI] = "write") \/ (~(nodeTS[VARI].tieBreaker = nodeTS[VARJ].tieBreaker)))


H_Inv130_R0_1_0 == \A VARJ \in H_NODES : (VARJ \in aliveNodes) \/ (~(nodeState[VARJ] = "replay"))
H_Inv3149_R0_2_1 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARJ] = "valid")) \/ (~(VARI \in aliveNodes))
H_Inv545_R0_2_2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \A MI \in msgsVAL : (MI.type = "VAL" => MI.version = nodeTS[VARI].version) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)) \/ ((VARJ \in aliveNodes))
H_Inv3135_R0_2_3 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARI] = "write") \/ (~(nodeTS[VARI].tieBreaker = nodeTS[VARJ].tieBreaker)))
H_Inv548_R0_2_4 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \A MI \in msgsVAL : (MI.type = "VAL" => MI.version = nodeTS[VARI].version) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)) \/ (~(nodeState[VARI] = "replay"))


H_Inv1274_R0_1_0 == \A VARJ \in H_NODES : \E VARK \in H_NODES : ~(VARK \in aliveNodes) \/ (~(nodeState[VARJ] = "replay"))
H_Inv369_R0_1_1 == \A VARJ \in H_NODES : (VARJ \in aliveNodes) \/ (~(nodeState[VARJ] = "replay"))
H_Inv1407_R0_2_2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \E VARK \in H_NODES : (nodeState[VARK] = "write") \/ (~(VARK \in aliveNodes) \/ (~(nodeTS[VARI].tieBreaker < nodeTS[VARJ].tieBreaker)))
H_Inv392_R0_2_3 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \E VARK \in H_NODES : \A VARMI \in msgsVAL : ((VARMI.type = "VAL") => VARMI.version = nodeTS[VARK].version) \/ (~(nodeState[VARJ] = "replay") \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version)))
H_Inv380_R0_2_4 == 
    \A VARI \in H_NODES : 
    \A VARJ \in H_NODES : 
    \E VARK \in H_NODES : 
    \A VARMI \in msgsVAL : 
        ((VARMI.type = "VAL") => VARMI.version = nodeTS[VARK].version) \/ (~(VARK \in aliveNodes) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)))

H_Inv700_R0_2_5 == 
    \A VARI \in H_NODES : 
    \A VARJ \in H_NODES : (VARJ \in aliveNodes) \/ ((nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARJ] = "valid")))

InvA == 
    \A VARI \in H_NODES : 
    \A VARJ \in H_NODES : 
    \A MI \in msgsVAL :
        (MI.type = "VAL" => MI.version = nodeTS[VARI].version) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)) \/ ((VARJ \in aliveNodes))


NewestVALMsg(m) == 
    \A m2 \in VALMsgs : 
        \/ <<m.version, m.tieBreaker>> = <<m2.version, m2.tieBreaker>>
        \/ greaterTS(m.version, m.tieBreaker, m2.version, m2.tieBreaker)

\* If a validate (VAL) message has been sent with value at version V, then all alive and valid nodes 
\* should match it (?)
H_VALMsgImpliesValidAliveNodesHaveEqualOrNewer == 
    \A m \in VALMsgs :
    \A n \in aliveNodes :
        \/ greaterTS(nodeTS[n].version, nodeTS[n].tieBreaker, m.version, m.tieBreaker) 
        \/ equalTS(nodeTS[n].version, nodeTS[n].tieBreaker, m.version, m.tieBreaker)

H_NewestVALMsgImpliesAllValidNodesMatchVersion == 
    \A m \in VALMsgs :
    \A n \in aliveNodes :
        (/\ NewestVALMsg(m) \* newest VAL message.
         /\ nodeState[n] = "valid") =>
            (/\ m.version = nodeTS[n].version
             /\ m.tieBreaker = nodeTS[n].tieBreaker)

H_VALMsgImpliesTieBreakerIsAlive == 
    \A m \in VALMsgs :  
        m.tieBreaker \in aliveNodes

\* \* For the newest VAL message, all alive nodes in the invalid state should
\* \* match its timestamp.
\* H_VALMsgImpliesInvalidAliveNodesHaveEqualOrNewer == 
\*     \A m \in VALMsgs :
\*     \A n \in aliveNodes :
\*         nodeState[n] \in {"invalid", "invalid_write", "write"} => 
\*             nodeTS[n].version >= m.version

\* If a node is in replay, then there cannot be a VAL message withs its timestamp.
H_VALMsgImpliesNoReplay == 
    \A m \in VALMsgs :
    \A n \in aliveNodes :
        nodeState[n] = "replay" => 
            ~(/\ nodeTS[n].version = m.version
              /\ nodeTS[n].tieBreaker = m.tieBreaker)

\* If a node is in write, and it has received ack from a node N, then N
\* must be in invalid state with an equal or higher timestamp.
H_ACKImpliesFreshTS == 
    \A ni,nj \in aliveNodes :
     (nodeState[ni] \in {"write"} /\ nj \in nodeRcvedAcks[ni]) => 
        /\ nodeState[nj] # "valid"
        /\ \/ equalTS(nodeTS[nj].version, nodeTS[nj].tieBreaker, nodeTS[ni].version, nodeTS[ni].tieBreaker)
           \/ greaterTS(nodeTS[nj].version, nodeTS[nj].tieBreaker, nodeTS[ni].version, nodeTS[ni].tieBreaker)

H_ACKImpliesFreshTSReplay == 
    \A ni,nj \in aliveNodes :
     (nodeState[ni] \in {"replay"} /\ nj \in nodeRcvedAcks[ni]) => 
        \* /\ nodeState[nj] # "valid"
        /\ \/ equalTS(nodeTS[nj].version, nodeTS[nj].tieBreaker, nodeTS[ni].version, nodeTS[ni].tieBreaker)
           \/ greaterTS(nodeTS[nj].version, nodeTS[nj].tieBreaker, nodeTS[ni].version, nodeTS[ni].tieBreaker)

H_ACKRecvd == 
    \A ni,nj \in aliveNodes : 
        (nj \in nodeRcvedAcks[ni] /\ nodeState[ni] \in {"write", "replay"}) => 
            \* /\ nodeState[ni] \in {"write", "replay"}
            /\ nodeState[nj] # "valid"

H_ACKSentImpliesSenderAsNew == 
    \A m \in msgsACK : 
        (m.type = "ACK") => 
            greaterOrEqualTS(nodeTS[m.sender].version, nodeTS[m.sender].tieBreaker, m.version, m.tieBreaker) 

H_AllAcksRecvdImpliesNewerTS ==
    \A n \in aliveNodes : 
    \A n2 \in aliveNodes :
        (receivedAllAcks(n) /\ nodeState[n] \in {"replay", "write"}) => 
            (greaterOrEqualTS(nodeTS[n2].version, nodeTS[n2].tieBreaker, nodeTS[n].version, nodeTS[n].tieBreaker)) 


H_Inv1439_R0_1_0 == 
    \A VARI \in aliveNodes : 
    \A VARMI \in msgsVAL : 
        ~((VARMI.type = "VAL") => greaterTS(VARMI.version, VARMI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)) \/ (~(NewestVALMsg(VARMI)))

\* HH_Inv4137_R0_1_2 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : ~(nodeState[VARI] = "replay") \/ (~(receivedAllAcks(VARI))) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version))

\* 
\* Support group of 3.
\* 

DummyFALSE == 2 > 3

HH_Inv859_R0_1_0 == 
    \A VARI \in aliveNodes : 
    \A VARJ \in aliveNodes : 
        ((nodeState[VARJ] = "valid"))  => 
            (\/ (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) 
             \/ ((nodeState[VARI] = "valid")))


HH_WriteNodeWithAllAcksImpliesAllAliveAreValid == 
    \A VARI \in aliveNodes : 
    \A VARJ \in aliveNodes : 
        (receivedAllAcks(VARI) /\ (nodeState[VARI] = "write")) => (nodeState[VARJ] # "valid")

HH_Inv776_R0_2_3 == 
    \A VARI \in aliveNodes : 
    \A VARJ \in aliveNodes : 
        \/ (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) 
        \/ (~(VARI \in nodeRcvedAcks[VARJ])) 
        \/ (~(nodeState[VARJ] = "replay"))


\* Another possible support group.
H_Inv1359_R0_1_0 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] = "valid")) \/ (~(VARJ \in aliveNodes))
H_Inv6807_R0_1_1 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : ~(nodeState[VARI] = "write") \/ (~(nodeState[VARJ] = "valid") \/ (~(receivedAllAcks(VARI))))
H_Inv6720_R0_1_2 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : ~(nodeState[VARI] = "replay") \/ (~(receivedAllAcks(VARI))) \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version))
H_Inv1319_R0_1_3 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(VARI \in nodeRcvedAcks[VARJ])) \/ (~(nodeState[VARJ] = "replay"))


H_Inv730_R0_1_0 == 
    \A VARI \in aliveNodes : 
    \A VARMI \in msgsVAL : 
        ((VARMI.type = "VAL") => 
            \/ equalTS(VARMI.version, VARMI.tieBreaker, nodeLastWriteTS[VARI].version, nodeLastWriteTS[VARI].tieBreaker)) 
            \/ ~(((VARMI.type = "VAL") => greaterTS(VARMI.version, VARMI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))

H_Inv874_R0_1_1 == 
    \A VARI \in aliveNodes : 
    \A VARMI \in msgsVAL : 
        ((VARMI.type = "VAL") => 
            \/ greaterTS(VARMI.version, VARMI.tieBreaker, nodeLastWriteTS[VARI].version, nodeLastWriteTS[VARI].tieBreaker)) 
            \/ ~(((VARMI.type = "VAL") => greaterTS(VARMI.version, VARMI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)))

H_Inv1293_R0_1_0 == 
    \A VARI \in aliveNodes : 
    \A VARMI \in msgsVAL : 
        ~((VARMI.type = "VAL") => greaterTS(VARMI.version, VARMI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)) \/ (~(NewestVALMsg(VARMI)))


H_Inv1534_R0_1_I1_1 == \A VARI \in aliveNodes : \A VARMVALI \in msgsVAL : ~((VARMVALI.type = "VAL") => greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker)) \/ ~(((VARMVALI.type = "VAL")))

H_Inv16595_R17_0_I3 == 
    \A VARI \in aliveNodes : 
    \A VARMINVI \in msgsINV : 
        (VARMINVI.tieBreaker = nodeTS[VARI].tieBreaker) 
            \/ (~(equalTS(VARMINVI.version, VARMINVI.tieBreaker, nodeLastWriteTS[VARI].version, nodeLastWriteTS[VARI].tieBreaker))) \/ (~(nodeState[VARI] \in {"write", "replay"}))


H_Inv1526_R20_0_I2 == \A VARI \in aliveNodes : (nodeWriteEpochID[VARI] = epochID) \/ (~(nodeState[VARI] = "replay"))


H_Inv40_R8_1_I2 == 
    \A VARI \in aliveNodes : 
        (Cardinality(aliveNodes) = 2) \/ (~(nodeState[VARI] = "replay"))


\* Invalid invariant.           
H_Inv231_R1_0_I2_0 == 
    \A VARI \in aliveNodes :
    \A VARJ \in aliveNodes :
    \A VARMVALI \in msgsVAL : 
        (VARMVALI.version = nodeTS[VARI].version) \/ ((nodeTS[VARI].version >= nodeTS[VARJ].version))

H_Inv26520_R4_0_I3_0 == 
    \A VARI \in aliveNodes : 
    \A VARJ \in aliveNodes : 
        ~(nodeState[VARI] = "replay") \/ (~(nodeState[VARJ] = "write") \/ (~(nodeTS[VARI] = nodeTS[VARJ])))

H_Inv32587_R4_0_I4_1 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : ~(VARI \in nodeRcvedAcks[VARJ]) \/ (~(nodeTS[VARI].tieBreaker = nodeTS[VARJ].tieBreaker)) \/ (~(nodeState[VARJ] \in {"write", "replay"})) \/ (~(nodeState[VARI] = "write"))

H_Inv45_R0_0_I1_0 == \A VARI \in aliveNodes : \A VARMVALI \in msgsVAL : ~(greaterTS(VARMVALI.version, VARMVALI.tieBreaker, nodeTS[VARI].version, nodeTS[VARI].tieBreaker))

H_Inv18827_R21_0_I3_0 == \A VARI \in aliveNodes : \A VARMINVI \in msgsINV : (VARMINVI.version = nodeTS[VARI].version) \/ (~(equalTS(VARMINVI.version, VARMINVI.tieBreaker, nodeLastWriteTS[VARI].version, nodeLastWriteTS[VARI].tieBreaker))) \/ (~(nodeState[VARI] = "write"))

H_Inv3300_R3_0_I2 == \A VARI \in aliveNodes : (nodeTS[VARI] = nodeLastWriteTS[VARI]) \/ (~(nodeState[VARI] \in {"write", "replay"}))


H_Inv10205_R1_0_I3 == \A VARI \in aliveNodes : \A VARJ \in aliveNodes : (greaterOrEqualTS(nodeTS[VARI].version, nodeTS[VARI].tieBreaker, nodeTS[VARJ].version, nodeTS[VARJ].tieBreaker)) \/ (~(receivedAllAcks(VARJ) /\ nodeRcvedAcks = nodeRcvedAcks)) \/ (~(nodeState[VARJ] = "replay"))

=============================================================================
