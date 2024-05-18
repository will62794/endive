------------------------------- MODULE ZeusReliableCommit -------------------------------
\* Specification of Zeus's reliable commit protocol presented in the Zeus paper 
\* that appears in Eurosys'21.
\* This module includes everything but the pipelining optimization presented in the paper.

\* Model check passed [@ 21st of Jan 2021] with the following parameters:
\*  R_NODES = {0, 1, 2}
\*  R_MAX_EPOCH = 4
\*  R_MAX_VERSION = 4

EXTENDS Integers, FiniteSets

CONSTANTS R_NODES,
          R_MAX_EPOCH,
          R_MAX_VERSION
  
VARIABLES rMsgsINV,
          rMsgsVAL,
          rMsgsACK,
          rKeyState,
          rKeySharers,
          rKeyVersion,
          rKeyRcvedACKs,
          rKeyLastWriter, 
          rNodeEpochID,
          rAliveNodes,
          rEpochID
          
vars == << rMsgsINV, rMsgsVAL, rMsgsACK, rKeyState, rKeySharers, rKeyVersion, rKeyRcvedACKs, 
           rKeyLastWriter, rNodeEpochID, rAliveNodes, rEpochID >>
-----------------------------------------------------------------------------
\* The consistent invariant: all alive nodes in valid state should have the same value / TS  
RConsistentInvariant ==
    \A k,s \in rAliveNodes:  \/ rKeyState[k] /= "valid"
                             \/ rKeyState[s] /= "valid" 
                             \/ rKeyVersion[k] = rKeyVersion[s]

RMaxVersionDistanceInvariant == \* this does not hold w/ the pipelining optimization
    \A k,s \in rAliveNodes:
                             \/ rKeyVersion[k] <= rKeyVersion[s] + 1
                             \/ rKeyVersion[s] <= rKeyVersion[k] + 1
 
RSingleOnwerInvariant == 
    \A k,s \in rAliveNodes:
                             \/ rKeySharers[k] /= "owner" 
                             \/ rKeySharers[s] /= "owner" 
                             \/ k = s

ROnwerOnlyWriterInvariant == 
    \A k \in rAliveNodes:
                             \/ rKeyState[k] /= "write" 
                             \/ rKeySharers[k] = "owner" 

ROnwerHighestVersionInvariant ==  \* owner has the highest version among alive nodes
    \A k,s \in rAliveNodes:
                            \/ /\ rKeySharers[s] /= "owner" 
                               /\ rKeySharers[k] /= "owner" 
                            \/ 
                               /\ rKeySharers[k] = "owner"
                               /\ rKeyVersion[k] >= rKeyVersion[s]
                            \/
                               /\ rKeySharers[s] = "owner"
                               /\ rKeyVersion[s] >= rKeyVersion[k]

-----------------------------------------------------------------------------

RMessageINV ==  \* Messages exchanged by the Protocol   
    [type: {"INV"}, 
     sender    : R_NODES,
     epochID   : Nat,
     version   : Nat] 

RMessageACK ==  \* Messages exchanged by the Protocol   
    [type: {"ACK"}, 
     sender    : R_NODES,
     epochID   : Nat,
     version   : Nat] 

RMessageVAL == [type: {"VAL"},        
                epochID   : Nat,
                version   : Nat] 
    
    
TypeOK ==  \* The type correctness invariant
    /\  rMsgsINV        \subseteq RMessageINV
    /\  rMsgsACK           \subseteq RMessageACK
    /\  rMsgsVAL           \subseteq RMessageVAL
    /\  rAliveNodes     \subseteq R_NODES
    /\  rKeyRcvedACKs  \in [R_NODES -> SUBSET R_NODES]
    /\  \A n \in R_NODES: rKeyRcvedACKs[n] \subseteq (R_NODES \ {n})
    /\  rNodeEpochID    \in [R_NODES -> Nat]
    /\  rKeyLastWriter  \in [R_NODES -> R_NODES]
    /\  rKeyVersion     \in [R_NODES -> Nat]
    /\  rKeySharers     \in [R_NODES -> {"owner", "reader", "non-sharer"}]
    /\  rKeyState       \in [R_NODES -> {"valid", "invalid", "write", "replay"}]
    /\ rEpochID \in Nat
    

Init == \* The initial predicate
    /\  rMsgsINV           = {}
    /\  rMsgsVAL          = {}
    /\  rMsgsACK           = {}
    /\  rEpochID        = 0
    /\  rAliveNodes     = R_NODES
    /\  rKeyVersion     = [n \in R_NODES |-> 0] 
    /\  rNodeEpochID    = [n \in R_NODES |-> 0] 
    /\  rKeyRcvedACKs   = [n \in R_NODES |-> {}]
    /\  rKeySharers     = [n \in R_NODES |-> "reader"] 
    /\  rKeyState       = [n \in R_NODES |-> "valid"]
    /\  rKeyLastWriter  = [n \in R_NODES |-> CHOOSE k \in R_NODES:
                                           \A m \in R_NODES: k <= m]

-----------------------------------------------------------------------------

RNoChanges_in_membership == UNCHANGED <<rAliveNodes, rEpochID>>
    
RNoChanges_but_membership ==
    UNCHANGED <<rMsgsINV, rMsgsVAL, rMsgsACK, rKeyState, rKeyVersion, 
                rKeyRcvedACKs, rKeyLastWriter, 
                rKeySharers, rNodeEpochID>>

RNoChanges ==
    /\  RNoChanges_in_membership 
    /\  RNoChanges_but_membership 

-----------------------------------------------------------------------------
\* A buffer maintaining all network messages. Messages are only appended to 
\* this variable (not \* removed once delivered) intentionally to check 
\* protocol's tolerance in dublicates and reorderings 
\* RSend(m) == rMsgs' = rMsgs \union {m}

\* Check if all acknowledgments for a write have been received                                                  
RAllACKsRcved(n) == (rAliveNodes \ {n}) \subseteq rKeyRcvedACKs[n]

RIsAlive(n) == n \in rAliveNodes 

RNodeFailure(n) == \* Emulate a node failure
\*    Make sure that there are atleast 3 alive nodes before killing a node
    /\ \E k,m \in rAliveNodes: /\ k /= n 
                               /\ m /= n
                               /\ m /= k
    /\ rEpochID' = rEpochID + 1
    /\ rAliveNodes' = rAliveNodes \ {n}
    /\ RNoChanges_but_membership

-----------------------------------------------------------------------------
RNewOwner(n) ==
    /\ rKeySharers[n] /= "owner"
    /\ \A x \in rAliveNodes: rNodeEpochID[x] = rEpochID \*TODO may move this to RNewOwner
    /\ \A k \in rAliveNodes: 
       /\ rKeySharers[k]        /= "owner"
       /\ \/ /\  rKeyState[k]    = "valid"       \* all alive replicas are in valid state
             /\  rKeySharers[k]  = "reader"      \* and there is not alive owner
          \/ /\  rKeySharers[k]  = "non-sharer"  \* and there is not alive owner
    /\ rKeySharers'              = [rKeySharers    EXCEPT ![n] = "owner"]
    /\ UNCHANGED <<rMsgsINV, rMsgsVAL, rMsgsACK, rKeyState, rKeyVersion, rKeyRcvedACKs, 
                   rKeyLastWriter, rAliveNodes, rNodeEpochID, rEpochID>>
       
ROverthrowOwner(n) ==
    \E k \in rAliveNodes: 
        /\ rKeySharers[n] /= "owner"
        /\ \A x \in rAliveNodes: rNodeEpochID[x] = rEpochID \*TODO may move this to RNewOwner
        /\ rKeyState[k]   = "valid"
        /\ rKeySharers[k] = "owner"
        /\ rKeySharers'   = [rKeySharers EXCEPT ![n] = "owner",
                                                ![k] = "reader"]
        /\ UNCHANGED <<rMsgsINV, rMsgsVAL, rMsgsACK, rKeyState, rKeyVersion, rKeyRcvedACKs,
                       rKeyLastWriter, rAliveNodes, rNodeEpochID, rEpochID>>

RGetOwnership(n) ==
    /\ rKeySharers[n] /= "owner"
    /\ \A x \in rAliveNodes: rNodeEpochID[x] = rEpochID \*TODO may move this to RNewOwner
    /\ \/  ROverthrowOwner(n) 
       \/  RNewOwner(n)    
-----------------------------------------------------------------------------

RRead(n) ==  \* Execute a read
    /\ rNodeEpochID[n] = rEpochID
    /\ rKeyState[n]    = "valid"
    /\ RNoChanges

RRcvInv(n, m) ==  \* Process a received invalidation
        /\ m \in rMsgsINV
        /\ m.type     = "INV"
        /\ m.epochID  = rEpochID
        /\ m.sender  /= n
        /\ m.sender  \in rAliveNodes
        \* always acknowledge a received invalidation (irrelevant to the timestamp)
        /\ rMsgsACK' = rMsgsACK \cup {([type       |-> "ACK",
                  epochID    |-> rEpochID,
                  sender     |-> n,   
                  version    |-> m.version])}
        /\ \/ m.version        > rKeyVersion[n]
              /\ rKeyState[n]   \in {"valid", "invalid", "replay"}
              /\ rKeyState'      = [rKeyState EXCEPT ![n] = "invalid"]
              /\ rKeyVersion'    = [rKeyVersion EXCEPT ![n]  = m.version]
              /\ rKeyLastWriter' = [rKeyLastWriter EXCEPT ![n] = m.sender]
           \/ m.version         <= rKeyVersion[n]
              /\ UNCHANGED <<rKeyState, rKeyVersion, rKeyLastWriter>>
        /\ UNCHANGED <<rMsgsINV, rMsgsVAL, rAliveNodes, rKeySharers, rKeyRcvedACKs, rNodeEpochID, rEpochID>>
            
RRcvVal(n, m) ==   \* Process a received validation
    /\ m \in rMsgsVAL
    /\ rKeyState[n] /= "valid"
    /\ m.type        = "VAL"
    /\ m.epochID     = rEpochID
    /\ m.version     = rKeyVersion[n]
    /\ rKeyState'    = [rKeyState EXCEPT ![n] = "valid"]
    /\ UNCHANGED <<rMsgsINV, rMsgsVAL, rMsgsACK, rKeyVersion, rKeyLastWriter, rKeySharers, rAliveNodes, rKeyRcvedACKs, rNodeEpochID, rEpochID>>
                       
\* RReaderActions(n) ==  \* Actions of a write follower
\*     \/ RRead(n)          
\*     \/ RRcvInv(n)
\*     \/ RRcvVal(n) 
    
-------------------------------------------------------------------------------------                       

RWrite(n) ==
    /\  rNodeEpochID[n]   =    rEpochID
    /\  rKeySharers[n]    \in  {"owner"} 
    /\  rKeyState[n]      \in  {"valid"} \* May add invalid state here as well
    /\  rKeyVersion[n]    <    R_MAX_VERSION
    /\  rKeyLastWriter'   =    [rKeyLastWriter  EXCEPT ![n] = n]
    /\  rKeyRcvedACKs'    =    [rKeyRcvedACKs   EXCEPT ![n] = {}]
    /\  rKeyState'        =    [rKeyState       EXCEPT ![n] = "write"]
    /\  rKeyVersion'      =    [rKeyVersion     EXCEPT ![n] = rKeyVersion[n] + 1]
    /\  rMsgsINV' = rMsgsINV \cup {([type        |-> "INV",
               epochID     |-> rEpochID,
               sender      |-> n,
               version     |-> rKeyVersion[n] + 1])}              
    /\ UNCHANGED <<rMsgsVAL, rMsgsACK, rAliveNodes, rKeySharers, rNodeEpochID, rEpochID>>

RRcvAck(n, m) ==   \* Process a received acknowledment
    /\ m \in rMsgsACK
    /\ m.type         =     "ACK"
    /\ m.epochID      =     rEpochID
    /\ m.sender      /=     n
    /\ m.version      =     rKeyVersion[n]
    /\ m.sender      \notin rKeyRcvedACKs[n]
    /\ rKeyState[n]  \in    {"write", "replay"}
    /\ rKeyRcvedACKs' =     [rKeyRcvedACKs    EXCEPT ![n] = rKeyRcvedACKs[n] \union {m.sender}]
    /\ UNCHANGED <<rMsgsINV, rMsgsVAL, rMsgsACK, rKeyState, rKeyVersion, rKeyLastWriter, rAliveNodes, rKeySharers, rNodeEpochID, rEpochID>>

RSendVals(n) == \* Send validations once received acknowledments from all alive nodes
    /\ rKeyState[n]     \in   {"write", "replay"}
    \* /\ RAllACKsRcved(n)
    /\ (rAliveNodes \ {n}) \subseteq rKeyRcvedACKs[n]
    /\ rKeyState'         =   [rKeyState EXCEPT![n] = "valid"]
    /\ rMsgsVAL' = rMsgsVAL \cup {([type        |-> "VAL", 
                              epochID     |-> rEpochID,
                              version     |-> rKeyVersion[n]])}
    /\ UNCHANGED <<rMsgsINV, rMsgsACK, rKeyRcvedACKs, rKeyVersion, rKeyLastWriter, rAliveNodes, rKeySharers, rNodeEpochID, rEpochID>>

\* ROwnerActions(n) ==   \* Actions of a read/write coordinator 
    \* \/ RRead(n)          
    \* \/ RWrite(n)         
    \* \/ RRcvAck(n)
    \* \/ RSendVals(n) 
    
------------------------------------------------------------------------------------- 
    
RWriteReplay(n) == \* Execute a write-replay
    /\  rKeyLastWriter'  =    [rKeyLastWriter   EXCEPT ![n] = n]
    /\  rKeyRcvedACKs'   =    [rKeyRcvedACKs    EXCEPT ![n] = {}]
    /\  rKeyState'       =    [rKeyState        EXCEPT ![n] = "replay"]
    /\  rMsgsINV' = rMsgsINV \cup {([type       |-> "INV",
               sender     |-> n,
               epochID    |-> rEpochID,
               version    |-> rKeyVersion[n]])}
    /\  UNCHANGED <<rMsgsVAL, rMsgsACK, rKeyVersion, rKeySharers, rAliveNodes, rNodeEpochID, rEpochID>>

RLocalWriteReplay(n) == 
    /\ rNodeEpochID[n] < rEpochID
    /\ \/ rKeySharers[n] = "owner" 
       \/ rKeyState[n]   = "replay"
    /\  rKeyLastWriter'  =    [rKeyLastWriter   EXCEPT ![n] = n]
    /\  rKeyRcvedACKs'   =    [rKeyRcvedACKs    EXCEPT ![n] = {}]
    /\  rKeyState'       =    [rKeyState        EXCEPT ![n] = "replay"]
    /\  rMsgsINV' = rMsgsINV \cup {([type       |-> "INV",
               sender     |-> n,
               epochID    |-> rEpochID,
               version    |-> rKeyVersion[n]])}
    /\  UNCHANGED <<rMsgsVAL, rMsgsACK, rKeyVersion, rKeySharers, rAliveNodes, rNodeEpochID, rEpochID>>
    
RFailedNodeWriteReplay(n) ==
    /\ rNodeEpochID[n] < rEpochID
    /\  ~RIsAlive(rKeyLastWriter[n])
    /\  rKeyState[n]     = "invalid"
    /\  rKeyLastWriter'  =    [rKeyLastWriter   EXCEPT ![n] = n]
    /\  rKeyRcvedACKs'   =    [rKeyRcvedACKs    EXCEPT ![n] = {}]
    /\  rKeyState'       =    [rKeyState        EXCEPT ![n] = "replay"]
    /\  rMsgsINV' = rMsgsINV \cup {([type       |-> "INV",
               sender     |-> n,
               epochID    |-> rEpochID,
               version    |-> rKeyVersion[n]])}
    /\  UNCHANGED <<rMsgsVAL, rMsgsACK, rKeyVersion, rKeySharers, rAliveNodes, rNodeEpochID, rEpochID>>

RUpdateLocalEpochID(n) ==
    /\ rNodeEpochID[n] < rEpochID
    /\ rKeyState[n]    = "valid" 
    /\ rNodeEpochID'   = [rNodeEpochID EXCEPT![n] = rEpochID]
    /\ UNCHANGED <<rMsgsINV, rMsgsVAL, rMsgsACK, rKeyState, rKeyVersion, rKeyRcvedACKs, 
                   rKeyLastWriter, rKeySharers, rAliveNodes, rEpochID>>

RReplayActions(n) ==
    /\ rNodeEpochID[n] < rEpochID
    /\ \/ RLocalWriteReplay(n)
       \/ RFailedNodeWriteReplay(n)
       \/ RUpdateLocalEpochID(n)
    

RRcvInvAction == \E n \in rAliveNodes, m \in rMsgsINV : RRcvInv(n, m)
RRcvValAction == \E n \in rAliveNodes : \E m \in rMsgsVAL : RRcvVal(n, m)
\* RReadAction == \E n \in rAliveNodes : RRead(n)
RWriteAction == \E n \in rAliveNodes : RWrite(n)
RRcvAckAction == \E n \in rAliveNodes, m \in rMsgsACK : RRcvAck(n, m)
RSendValsAction == \E n \in rAliveNodes : RSendVals(n)
RLocalWriteReplayAction == \E n \in rAliveNodes : RLocalWriteReplay(n)
RFailedNodeWriteReplayAction == \E n \in rAliveNodes : RFailedNodeWriteReplay(n)
RUpdateLocalEpochIDAction == \E n \in rAliveNodes : RUpdateLocalEpochID(n)
ROverthrowOwnerAction == \E n \in rAliveNodes : ROverthrowOwner(n)
RNewOwnerAction == \E n \in rAliveNodes : RNewOwner(n)
RNodeFailureAction == \E n \in rAliveNodes : RNodeFailure(n)

------------------------------------------------------------------------------------- 
Next == \* Modeling protocol (Owner and Reader actions while emulating failures)
    \/ RRcvInvAction
    \/ RRcvValAction
    \* \/ RReadAction          
    \/ RWriteAction         
    \/ RRcvAckAction
    \/ RSendValsAction
    \/ RLocalWriteReplayAction
    \/ RFailedNodeWriteReplayAction
    \/ RUpdateLocalEpochIDAction
    \/ ROverthrowOwnerAction
    \/ RNewOwnerAction
    \/ RNodeFailureAction


(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

Invariants == /\ ([]TypeOK) 
              /\ ([]RConsistentInvariant)
              /\ ([]RSingleOnwerInvariant)
              /\ ([]ROnwerOnlyWriterInvariant)
              /\ ([]RMaxVersionDistanceInvariant)
              /\ ([]ROnwerHighestVersionInvariant)

THEOREM Spec => Invariants

CTICost == 0
NextUnchanged == UNCHANGED vars

H_Safety == 
    /\ RConsistentInvariant
    /\ RSingleOnwerInvariant
    /\ ROnwerOnlyWriterInvariant
    /\ RMaxVersionDistanceInvariant
    /\ ROnwerHighestVersionInvariant

\* 
\* Other lemmas.
\* 

H_Inv1442_R0_1_I3 == 
    \A VARI \in rAliveNodes : 
    \A VARJ \in rAliveNodes : 
        (rKeyState[VARI] = "invalid") \/ (~((rAliveNodes \ {VARI}) \subseteq rKeyRcvedACKs[VARI])) \/ ((rKeyVersion[VARI] <= rKeyVersion[VARJ]))


H_Inv2933_R0_1_I3 == 
    \A VARI \in rAliveNodes : 
    \A VARJ \in rAliveNodes : 
        (~(VARJ \in rKeyRcvedACKs[VARI])) \/ (rKeyState[VARI] = "invalid") \/ ((rKeyVersion[VARI] <= rKeyVersion[VARJ]))

A_Inv741 == \A VARI \in rAliveNodes : ~(Cardinality(rAliveNodes) > 2) \/ (~(rKeyState[VARI] = "replay")) 
A_Inv766 == \A VARI \in rAliveNodes : \A VARJ \in rAliveNodes : ~(VARI # VARJ /\ rKeyState[VARI] = "write") \/ (~(rKeyState[VARJ] = "write"))

H1 == 
    \A VARI \in rAliveNodes : 
    \* \A VARJ \in rAliveNodes : 
    \A VARMINV \in rMsgsINV : 
        \* (rKeyState[VARI] = "valid") => (VARMINV.version <= rKeyVersion[VARI]) 
        (rKeyState[VARI] = "valid" /\ rKeySharers[VARI] = "owner") => (VARMINV.version <= rKeyVersion[VARI]) 

H_Inv1205_R0_2_I1 == 
    /\ \A VARI \in rAliveNodes : 
       \A VARMINV \in rMsgsINV : 
            (rKeyState[VARI] = "write") => (VARMINV.version <= rKeyVersion[VARI]) 
    \* /\ H1


H_Inv57_R0_2_I1 == \A VARMINV \in rMsgsINV : ~(VARMINV.version > rKeyVersion[VARMINV.sender])

RInv274 == \A VARMINV \in rMsgsINV : (VARMINV.epochID < rEpochID) \/ ((VARMINV.epochID = rEpochID))
=============================================================================
