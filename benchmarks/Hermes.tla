------------------------------- MODULE Hermes -------------------------------
\* 
\* Spec source: https://github.com/ease-lab/Hermes
\* 

EXTENDS     Integers,
            FiniteSets

CONSTANTS   H_NODES,
            H_MAX_VERSION
            
VARIABLES   msgs,
            nodeTS,
            nodeState, 
            nodeRcvedAcks,
            nodeLastWriter,
            nodeLastWriteTS,
            nodeWriteEpochID, 
            aliveNodes,
            epochID 
            
\* all Hermes (+ environment) variables
hvars == << msgs, nodeTS, nodeState, nodeRcvedAcks, nodeLastWriter, 
            nodeLastWriteTS, nodeWriteEpochID, aliveNodes, epochID >>

-------------------------------------------------------------------------------------

\* Invalidation (INV) messages are broadcast when a write comes in that
\* cannot be completed due to a node not currently being in a valid state.
INVMessage == [
    type: {"INV"}, 
    sender    : H_NODES,
    epochID   : 0..(Cardinality(H_NODES) - 1),
    version   : 0..H_MAX_VERSION,  
    tieBreaker: H_NODES
] 

\* Acknowledgment (ACK) messages are sent by nodes back to 
\* the coordinator to acknowledge the receipt of an INV message.
\* Once the coordinator receives ACKS from all live replicas, the 
\* write is completed by transitioning the key to the Valid state.
ACKMessage == [
    type: {"ACK"}, 
    sender    : H_NODES,
    epochID   : 0..(Cardinality(H_NODES) - 1),
    version   : 0..H_MAX_VERSION,  
    tieBreaker: H_NODES
]

\* After receipt of enough ACK messages, a coordinator will broadcast a VAL
\* message with the key and the same timestamp to all followers.
VALMessage == [
    type: {"VAL"},        \* optimization: epochID is not required for VALs
                          \* epochID   : 0..(Cardinality(H_NODES) - 1),
    version   : 0..H_MAX_VERSION, 
    tieBreaker: H_NODES    
]

Message ==  INVMessage \cup ACKMessage \cup VALMessage

TypeOK ==  \* The type correctness invariant
    /\ msgs \in Message
    /\ nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES]
    /\ \A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n})
    /\  nodeLastWriter  \in [H_NODES -> H_NODES]
    /\  nodeLastWriteTS \in [H_NODES -> [version : 0..H_MAX_VERSION, tieBreaker: H_NODES ]]
    /\  nodeTS          \in [H_NODES -> [version : 0..H_MAX_VERSION, tieBreaker: H_NODES ]]
    /\  nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}]
    \*  membership and epoch id related
    /\  aliveNodes      \in SUBSET H_NODES
    /\  epochID         \in 0..(Cardinality(H_NODES) - 1)
    /\  nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)]

Init == \* The initial predicate
    /\  msgs            = {}
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
send(m) == msgs' = msgs \union {m}

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
       
isAlive(n) == n \in aliveNodes
                   
nodeFailure(n) == \* Emulate a node failure
\*    Make sure that there are atleast 3 alive nodes before killing a node
    /\ Cardinality(aliveNodes) > 2
    /\ aliveNodes' = aliveNodes \ {n}
    /\ epochID'     = epochID + 1
    /\ UNCHANGED <<msgs, nodeState, nodeTS, nodeLastWriter, 
                   nodeLastWriteTS, nodeRcvedAcks, nodeWriteEpochID>>

h_upd_not_aliveNodes ==
    /\  UNCHANGED <<aliveNodes, epochID, nodeWriteEpochID>>
    
    
h_upd_aliveNodes ==
    /\ UNCHANGED <<msgs, nodeState, nodeTS, nodeLastWriter, nodeLastWriteTS, nodeRcvedAcks>>
                   
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
                                            
h_send_inv_or_ack(n, newVersion, newTieBreaker, msgType) ==  
    /\  send([type        |-> msgType,
              epochID     |-> epochID, \* we always use the latest epochID
              sender      |-> n,
              version     |-> newVersion, 
              tieBreaker  |-> newTieBreaker])              

h_actions_for_upd(n, newVersion, newTieBreaker, newState, newAcks) == \* Execute a write
    /\  h_upd_state(n, newVersion, newTieBreaker, newState, newAcks)
    /\  h_send_inv_or_ack(n, newVersion, newTieBreaker, "INV")
    /\  UNCHANGED <<aliveNodes, epochID>>
 

h_actions_for_upd_replay(n, acks) == \* Apply a write-replay using same TS (version, tie-breaker) 
                                     \* and either reset acks or keep already gathered acks
    /\  h_actions_for_upd(n, nodeTS[n].version, nodeTS[n].tieBreaker, "replay", acks)

-------------------------------------------------------------------------------------

HRead(n) ==  \* Execute a read
    /\ nodeState[n] = "valid"
    /\ h_upd_nothing
              
HWrite(n) == \* Execute a write
\*    /\  nodeState[n]      \in {"valid", "invalid"} 
    \* writes in invalid state are also supported as an optimization
    /\  nodeState[n]      \in {"valid"}
    /\  nodeTS[n].version < H_MAX_VERSION \* Only to configurably terminate the model checking 
    /\  h_actions_for_upd(n, nodeTS[n].version + 1, n, "write", {})


HCoordWriteReplay(n) == \* Execute a write-replay after a membership re-config
    /\  nodeState[n] \in {"write", "replay"}
    /\  nodeWriteEpochID[n] < epochID
    /\  ~receivedAllAcks(n) \* optimization to not replay when we have gathered acks from all alive
    /\  h_actions_for_upd_replay(n, nodeRcvedAcks[n])


HRcvAck(n) ==   \* Process a received acknowledment
    \E m \in msgs: 
        /\ m.type     = "ACK"
        /\ m.epochID  = epochID
        /\ m.sender  /= n
        /\ m.sender  \notin nodeRcvedAcks[n]
        /\ equalTS(m.version, m.tieBreaker,
                   nodeLastWriteTS[n].version, 
                   nodeLastWriteTS[n].tieBreaker)
        /\ nodeState[n] \in {"write", "invalid_write", "replay"}
        /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = 
                                              nodeRcvedAcks[n] \union {m.sender}]
        /\ UNCHANGED <<msgs, nodeLastWriter, nodeLastWriteTS, 
                       aliveNodes, nodeTS, nodeState, epochID, nodeWriteEpochID>>


HSendVals(n) == \* Send validations once acknowledments are received from all alive nodes
    /\ nodeState[n] \in {"write", "replay"}
    /\ receivedAllAcks(n)
    /\ nodeState'         = [nodeState EXCEPT![n] = "valid"]
    /\ send([type        |-> "VAL", 
             version     |-> nodeTS[n].version, 
             tieBreaker  |-> nodeTS[n].tieBreaker])
    /\ UNCHANGED <<nodeTS, nodeLastWriter, nodeLastWriteTS,
                   aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>
 
HCoordinatorActions(n) ==   \* Actions of a read/write coordinator 
    \/ HRead(n)          
    \/ HCoordWriteReplay(n) \* After failures
    \/ HWrite(n)         
    \/ HRcvAck(n)
    \/ HSendVals(n) 

-------------------------------------------------------------------------------------               
    
HRcvInv(n) ==  \* Process a received invalidation
    \E m \in msgs: 
        /\ m.type     = "INV"
        /\ m.epochID  = epochID
        /\ m.sender  /= n
        \* always acknowledge a received invalidation (irrelevant to the timestamp)
        /\ send([type       |-> "ACK",
                 sender     |-> n,   
                 epochID    |-> epochID,
                 version    |-> m.version,
                 tieBreaker |-> m.tieBreaker])
        /\ IF greaterTS(m.version, m.tieBreaker,
                        nodeTS[n].version, nodeTS[n].tieBreaker)
           THEN   /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
                  /\ nodeTS' = [nodeTS EXCEPT ![n].version    = m.version,
                                          ![n].tieBreaker = m.tieBreaker]
                  /\ IF nodeState[n] \in {"valid", "invalid", "replay"}
                     THEN 
                        nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                     ELSE 
                        nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
           ELSE
                  UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeWriteEpochID>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>
     
            
HRcvVal(n, m) ==   \* Process a received validation
    /\ m \in msgs
    /\ nodeState[n] /= "valid"
    /\ m.type = "VAL"
    /\ equalTS(m.version, m.tieBreaker,
                nodeTS[n].version, 
                nodeTS[n].tieBreaker)
    /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
    /\ UNCHANGED <<msgs, nodeTS, nodeLastWriter, nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>

HFollowerWriteReplay(n) == \* Execute a write-replay when coordinator failed
    /\  nodeState[n] \in {"invalid", "invalid_write"}
    /\  ~isAlive(nodeLastWriter[n])
    /\  h_actions_for_upd_replay(n, {}) 

   
HFollowerActions(n, m) ==  \* Actions of a write follower
    \/ HRcvInv(n)
    \/ HFollowerWriteReplay(n)
    \/ HRcvVal(n, m) 
 
------------------------------------------------------------------------------------- 

HRcvInvAction == TRUE /\ \E n \in aliveNodes : HRcvInv(n)
HFollowerWriteReplayAction == TRUE /\ \E n \in aliveNodes : HFollowerWriteReplay(n)
HRcvValAction == TRUE /\ \E n \in aliveNodes, m \in msgs : HRcvVal(n, m)
HReadAction == TRUE /\ \E n \in aliveNodes : HRead(n)
HCoordWriteReplayAction == TRUE /\ \E n \in aliveNodes : HCoordWriteReplay(n)
HWriteAction == TRUE /\ \E n \in aliveNodes : HWrite(n)
HRcvAckAction == TRUE /\ \E n \in aliveNodes : HRcvAck(n)
HSendValsAction == TRUE /\ \E n \in aliveNodes : HSendVals(n)
HNodeFailureAction == TRUE /\ \E n \in aliveNodes : nodeFailure(n)

Next == \* Hermes (read/write) protocol (Coordinator and Follower actions) + failures
    \* Follower actions.
    \/ HRcvInvAction
    \/ HFollowerWriteReplayAction
    \/ HRcvValAction
    \* Coordinator actions (leader of writes/reads)
    \/ HReadAction
    \/ HCoordWriteReplayAction
    \/ HWriteAction
    \/ HRcvAckAction
    \/ HSendValsAction
    \* Failure actions.
    \/ HNodeFailureAction


Spec == Init /\ [][Next]_hvars


\* The consistent invariant: all alive nodes in valid state should have the same value / TS         
HConsistent == 
    \A k,s \in aliveNodes:  
        (nodeState[k] = "valid" /\ nodeState[s] = "valid") => nodeTS[k] = nodeTS[s]



\* THEOREM H_Spec =>([]HTypeOK) /\ ([]HConsistent)

NextUnchanged == UNCHANGED hvars


\* 
\* Lemmas for inductive invariant.
\* 

H_Inv18_1_0 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (VARI \in aliveNodes) \/ (~(nodeState[VARI] = "replay"))
H_Inv2558_2_1 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(VARI \in aliveNodes)) \/ (~(nodeState[VARJ] = "valid"))
H_Inv2587_2_2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARI] = "write") \/ (~(nodeTS[VARI].tieBreaker = nodeTS[VARJ].tieBreaker)))


H_Inv130_R0_1_0 == \A VARJ \in H_NODES : (VARJ \in aliveNodes) \/ (~(nodeState[VARJ] = "replay"))
H_Inv3149_R0_2_1 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARJ] = "valid")) \/ (~(VARI \in aliveNodes))
H_Inv545_R0_2_2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \A MI \in msgs : (MI.type = "VAL" => MI.version = nodeTS[VARI].version) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)) \/ ((VARJ \in aliveNodes))
H_Inv3135_R0_2_3 == \A VARI \in H_NODES : \A VARJ \in H_NODES : (nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARI] = "write") \/ (~(nodeTS[VARI].tieBreaker = nodeTS[VARJ].tieBreaker)))
H_Inv548_R0_2_4 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \A MI \in msgs : (MI.type = "VAL" => MI.version = nodeTS[VARI].version) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)) \/ (~(nodeState[VARI] = "replay"))


H_Inv1274_R0_1_0 == \A VARJ \in H_NODES : \E VARK \in H_NODES : ~(VARK \in aliveNodes) \/ (~(nodeState[VARJ] = "replay"))
H_Inv369_R0_1_1 == \A VARJ \in H_NODES : (VARJ \in aliveNodes) \/ (~(nodeState[VARJ] = "replay"))
H_Inv1407_R0_2_2 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \E VARK \in H_NODES : (nodeState[VARK] = "write") \/ (~(VARK \in aliveNodes) \/ (~(nodeTS[VARI].tieBreaker < nodeTS[VARJ].tieBreaker)))
H_Inv392_R0_2_3 == \A VARI \in H_NODES : \A VARJ \in H_NODES : \E VARK \in H_NODES : \A VARMI \in msgs : ((VARMI.type = "VAL") => VARMI.version = nodeTS[VARK].version) \/ (~(nodeState[VARJ] = "replay") \/ (~(nodeTS[VARI].version > nodeTS[VARJ].version)))
H_Inv380_R0_2_4 == 
    \A VARI \in H_NODES : 
    \A VARJ \in H_NODES : 
    \E VARK \in H_NODES : 
    \A VARMI \in msgs : 
        ((VARMI.type = "VAL") => VARMI.version = nodeTS[VARK].version) \/ (~(VARK \in aliveNodes) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)))

H_Inv700_R0_2_5 == 
    \A VARI \in H_NODES : 
    \A VARJ \in H_NODES : (VARJ \in aliveNodes) \/ ((nodeTS[VARI].version >= nodeTS[VARJ].version) \/ (~(nodeState[VARJ] = "valid")))

InvA == 
    \A VARI \in H_NODES : 
    \A VARJ \in H_NODES : 
    \A MI \in msgs :
        (MI.type = "VAL" => MI.version = nodeTS[VARI].version) \/ (~(nodeTS[VARI].version < nodeTS[VARJ].version)) \/ ((VARJ \in aliveNodes))


VALMsgs == {m \in msgs : m.type = "VAL"} 

NewestVALMsg(m) == 
    \A m2 \in VALMsgs : 
        \/ <<m.version, m.tieBreaker>> = <<m2.version, m2.tieBreaker>>
        \/ greaterTS(m.version, m.tieBreaker, m2.version, m2.tieBreaker)

\* If a validate (VAL) message has been sent with value at version V, then all alive and valid nodes 
\* should match it (?)
H_VALMsgImpliesValidAliveNodesHaveEqualOrNewer == 
    \A m \in VALMsgs :
    \A n \in aliveNodes :
        nodeTS[n].version >= m.version 

H_VALMsgImpliesSomeValidNodeWithVersion == 
    \A m \in VALMsgs :
        \* This is the newest VAL message.
        (\A m2 \in VALMsgs : 
            \/ <<m.version, m.tieBreaker>> = <<m2.version, m2.tieBreaker>>
            \/ greaterTS(m.version, m.tieBreaker, m2.version, m2.tieBreaker)) =>
            (\A n \in aliveNodes : 
                nodeState[n] = "valid" => 
                    /\ m.version = nodeTS[n].version
                    /\ m.tieBreaker = nodeTS[n].tieBreaker)

\* For the newest VAL message, all alive nodes in the invalid state should
\* match its timestamp.
H_VALMsgImpliesInvalidAliveNodesHaveEqualOrNewer == 
    \A m \in VALMsgs :
    \A n \in aliveNodes :
        nodeState[n] = "invalid" => 
            nodeTS[n].version >= m.version

\* If a node is in replay, then there cannot be a VAL message withs its timestamp.
H_VALMsgImpliesNoReplay == 
    \A m \in VALMsgs :
    \A n \in aliveNodes :
        nodeState[n] = "replay" => 
            ~(/\ nodeTS[n].version = m.version
              /\ nodeTS[n].tieBreaker = m.tieBreaker)

\* If a node is in write, and it has received ack from a node N, then N
\* must be in invalid state with an equal or higher timestamp.
\* Not correct yet.
H_ACKImpliesInvalidWrite == 
    \A ni,nj \in aliveNodes :
     (nodeState[ni] = "write" /\ nj \in nodeRcvedAcks[ni]) => 
        /\ nodeState[nj] = "invalid"
        /\ nodeTS[nj].version >= nodeTS[ni].version
        /\ nodeTS[nj].tieBreaker = nodeTS[ni].tieBreaker

=============================================================================
