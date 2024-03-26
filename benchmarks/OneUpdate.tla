--------------------------- MODULE OneUpdate ---------------------------

\* This module is a formal specification of 1-Update, 
\* a hybrid invalidate and update cache coherence protocol that appears in PACT'21. 
\* This spec actually includes two variants of 1-Update one in which acks for updates 
\* are gathered directly by the directory (the main variant discussed in the paper);
\* and another variant where acks for updates are gathered by the writer itself.
\* Setting the constant ENABLE_DIR_ACKS TRUE or FALSE verifies either variant accordingly.

EXTENDS     Integers, FiniteSets

CONSTANTS   CORES, 
            MAX_WRITES,
            WRITE_TO_UPDATE, \* I.e., number of write on which we will trigger the Update
            ENABLE_DIR_ACKS  \* - If TRUE:  update acks are gathered by the directory. 
                             \* - If FALSE: update acks are gathered by the writer.

VARIABLES   \* variable prefixes --> g:global, d: directory, c: cache/core | VECTORS indexed by cache/core_id
            \* GLOBAL variables 
            Msgs,
            gBcstMsg,
            gBcstMsgRcvers,
            \* Dir variables 
            dOwner,
            dSharers,    \* No sharers/owner: .readers = {} / .owner = 0 
            dReqPending,
            dState,
            dRcvAcks,
            \* Cache/core variables 
            cState,
            cRcvAcks,
            \* data is a monotonically increasing int to check correctness invariants
            cData, 
            mData \* Memory data 

vars == <<dOwner, dSharers, dReqPending, dState, dRcvAcks,
          cState, cRcvAcks, cData, 
          mData, Msgs, gBcstMsg, gBcstMsgRcvers >>

\* Helper Definitions
EMPTY_OWNER   == 0

\* Assumptions
ASSUME Cardinality(CORES) > 0 \* assume atleast 1 cache
ASSUME MAX_WRITES > WRITE_TO_UPDATE \* ensure we always have enough writes to trigger an update
ASSUME EMPTY_OWNER \notin CORES \* id used for EMPTY_ONWER should not be used to identify a CORE
ASSUME ENABLE_DIR_ACKS \in {TRUE, FALSE}
-------------------------------------------------------------------------------------
\* Useful Unchanged shortcuts
unchanged_g       == UNCHANGED <<gBcstMsg, gBcstMsgRcvers>>
unchanged_m       == UNCHANGED <<mData>>
unchanged_c       == UNCHANGED <<cState, cRcvAcks, cData>>
unchanged_d       == UNCHANGED <<dOwner, dSharers, dReqPending, dState, dRcvAcks>>
unchanged_dm      == unchanged_d /\ unchanged_m
unchanged_cm      == unchanged_c /\ unchanged_m 
unchanged_cd      == unchanged_c /\ unchanged_d 
unchanged_mcd     == unchanged_c /\ unchanged_d /\ unchanged_m

unchanged_gm      == unchanged_g /\ unchanged_m 
unchanged_gmc     == unchanged_c /\ unchanged_gm 
unchanged_gmd     == unchanged_d /\ unchanged_gm 

unchanged_Msgs    == UNCHANGED <<Msgs>>
unchanged_mMsgs   == unchanged_Msgs /\ unchanged_m   
unchanged_cMsgs   == unchanged_Msgs /\ unchanged_c   
unchanged_dMsgs   == unchanged_Msgs /\ unchanged_d   
unchanged_dmMsgs  == unchanged_Msgs /\ unchanged_dm  
unchanged_cmMsgs  == unchanged_Msgs /\ unchanged_cm  
unchanged_cdMsgs  == unchanged_Msgs /\ unchanged_cd  
unchanged_mcdMsgs == unchanged_Msgs /\ unchanged_mcd 

unchanged_gMsgs    == unchanged_g /\ unchanged_Msgs 
unchanged_gmMsgs   == unchanged_g /\ unchanged_mMsgs   
unchanged_gcMsgs   == unchanged_g /\ unchanged_cMsgs   
unchanged_gdMsgs   == unchanged_g /\ unchanged_dMsgs   
unchanged_gdmMsgs  == unchanged_g /\ unchanged_dmMsgs  
unchanged_gcmMsgs  == unchanged_g /\ unchanged_cmMsgs  
unchanged_gcdMsgs  == unchanged_g /\ unchanged_cdMsgs  
unchanged_gmcdMsgs == unchanged_g /\ unchanged_mcdMsgs

-------------------------------------------------------------------------------------
\* Type definitions
Type_binary   == 0..1
Type_Data     == 0..MAX_WRITES
Type_State    == {"M", "0", "E", "S", "I"} \* all nodes start from I

\* Msgs send by requester
Type_rMsg ==  
    [type: {"GetS", "GetM"}, sender : CORES] 

Type_uMsg ==  
    [type: {"Upd"},           data : Type_Data,
                              sender   : CORES,
                              receiver : CORES] 
\* Msgs send by directory
Type_iMsg ==
    [type: {"DInv"},          sender   : CORES, \* initial sender (i.e., requester)
                              receiver : CORES]        

Type_dMsg ==  Type_iMsg \union 
    [type: {"Fwd-GetM", "Fwd-GetS"}, 
                              sender   : CORES, \* initial sender (i.e., requester)
                              receiver : CORES] 

\* Msgs send by sharer
Type_sMsg ==  
    [type: {"SAck, UAck"},    sender   : CORES,
                              receiver : CORES] 
    \union
    [type: {"SData", 
            "SAckData"},      data : Type_Data,
                              sender   : CORES,
                              receiver : CORES]

Type_bcastMsg == Type_uMsg \union Type_iMsg 
Type_msg == Type_sMsg 
     \union Type_rMsg 
     \union Type_uMsg 
     \union Type_iMsg 
     \union Type_dMsg 
     \union Type_sMsg 
 
-------------------------------------------------------------------------------------
\* Type check and initialization
   
ATypeOK ==  \* The type correctness invariant
            \* GLOBAL variables 
           /\ Msgs           \subseteq Type_msg
           /\ gBcstMsg       \in  Type_bcastMsg 
           /\ gBcstMsgRcvers \subseteq CORES
            \* Directory/memory variables 
           /\ dOwner         \in CORES
           /\ dSharers       \subseteq CORES
           /\ dRcvAcks       \subseteq CORES
           /\ dReqPending    \in Type_binary
           /\ dState         \in Type_State
           /\ cState         \in Type_State
           /\ mData          \in Type_Data
            \* Core/cache variables 
           /\ \A n \in CORES : cData[n]      \in Type_Data
           /\ \A n \in CORES : cState[n]     \in Type_State
           /\ \A n \in CORES : cRcvAcks[n]   \subseteq (CORES \ {n})

Init == \* The initial predicate
            \* GLOBAL variables 
           /\ Msgs           = {}
           /\ gBcstMsg       = {}
           /\ gBcstMsgRcvers = {}
            \* Directory/memory variables 
           /\ mData       = 0
           /\ dState      = "I"
           /\ dOwner      = EMPTY_OWNER 
           /\ dSharers    = {}
           /\ dRcvAcks    = {}
           /\ dReqPending = 0
            \* Core/cache variables 
           /\ cData       = [n \in CORES |-> 0]
           /\ cRcvAcks    = [n \in CORES |-> {}]
           /\ cState      = [n \in CORES |-> "I"]
              
-------------------------------------------------------------------------------------
\* TODO may add sanity check that m already exists in the set before delivering it
deliver_Msg(m)  == Msgs' = Msgs  \ {m}  

\* TODO may add all messages to one set from which we do not remove msgs for debugging (w/ a global counter)
_send_Msg(m) == Msgs' = Msgs \union {m}  


_send_Msg_with_data(_type, _sender, _receiver, _data) ==
        _send_Msg([type     |-> _type,
                   data     |-> _data,
                   sender   |-> _sender,
                   receiver |-> _receiver])              

_send_Msg_simple(_type, _requester, _receiver) ==
        _send_Msg([type      |-> _type,
                   sender    |-> _requester,
                   receiver  |-> _receiver])              

_resp_Msg(m, new_m)  == Msgs' = (Msgs  \ {m})  \union {new_m}
_resp_Msg_simple(m, _type) == 
        _resp_Msg(m, [type      |-> _type,
                      sender    |-> m.receiver,
                      receiver  |-> m.sender])
_resp_Msg_with_data(m, _type) == 
        _resp_Msg(m, [type      |-> _type,
                      data      |-> cData[m.receiver],
                      sender    |-> m.receiver,
                      receiver  |-> m.sender])

resp_UAck(m)     == _resp_Msg_simple(m, "UAck")              
resp_SAck(m)     == _resp_Msg_simple(m, "SAck")              
resp_SData(m)    == _resp_Msg_with_data(m, "SData")
resp_SDataAck(m) == _resp_Msg_with_data(m, "SDataAck")


ucst_FwdGetM(_requester, _receiver) == 
        _send_Msg_simple("Fwd-GetM", _requester, _receiver)
ucst_FwdGetS(_requester, _receiver) == 
        _send_Msg_simple("Fwd-GetS", _requester, _receiver)


_bcst_msg(_requester, _receivers, _msg) == 
        LET rcver == CHOOSE x \in _receivers : TRUE IN 
            /\ gBcstMsgRcvers' = _receivers \ {rcver}
            /\ gBcstMsg'= {[_msg EXCEPT!.receiver = rcver]}

bcst_DInv(_requester, _receivers) == 
        _bcst_msg(_requester, _receivers, 
                        [type     |-> "DInv",
                         sender   |-> _requester,
                         receiver |-> 0])

bcst_Upd(_requester, _receivers, _data) == 
        _bcst_msg(_requester, _receivers, 
                        [type     |-> "Upd",
                         data     |-> _data,
                         sender   |-> _requester,
                         receiver |-> 0])


rcv_unicast(m, receiver, type) ==
            /\ m.type = type
            /\ m.receiver = receiver

rcv_UAck(m, receiver)     == rcv_unicast(m, receiver, "UAck")
rcv_SAck(m, receiver)     == rcv_unicast(m, receiver, "SAck")
rcv_SData(m, receiver)    == rcv_unicast(m, receiver, "SData")
rcv_SDataAck(m, receiver) == rcv_unicast(m, receiver, "SDataAck")

rcv_Upd(m, receiver)      == rcv_unicast(m, receiver, "Upd")
rcv_DInv(m, receiver)     == rcv_unicast(m, receiver, "DInv")

rcv_FwdGetM(m, receiver)  == rcv_unicast(m, receiver, "Fwd-GetM")
rcv_FwdGetS(m, receiver)  == rcv_unicast(m, receiver, "Fwd-GetS")

-------------------------------------------------------------------------------------
\* Helper functions
is_M(n) == cState[n] = "M"
is_O(n) == cState[n] = "O"
is_E(n) == cState[n] = "E"
is_S(n) == cState[n] = "S"
is_I(n) == cState[n] = "I"

dir_rcved_acks_from_set(set) ==  set             \subseteq dRcvAcks
rcved_acks_from_set(n,  set) ==  set             \subseteq cRcvAcks[n]
rcved_all_sharer_acks(n)     == (dSharers \ {n}) \subseteq cRcvAcks[n]

has_valid_data(n)            == ~is_I(n)
set_next_data_value(n)       == cData' = [cData EXCEPT![n] = cData[n] + 1]
has_not_reached_final_value  == \A n \in CORES : cData[n] < MAX_WRITES + 1

\* todo check the correctness of the following 
is_sharer(n)    == ~is_I(n)
is_exclusive(n) ==  is_M(n) \/ is_E(n)  
is_owner(n)     ==  is_O(n) \/ is_M(n)

upd_core_data(n, _data) == cData' = [cData EXCEPT![n] = _data]
rd_mem_data(n)  == upd_core_data(n, mData)
upd_mem_data(n) == mData' = cData[n]

Min(S) == CHOOSE x \in S: 
            \A y \in S \ {x}: 
              y > x
-------------------------------------------------------------------------------------
\* Protocol Invariants: 

\* memory data consistency invariant
MEM_DATA_CONSISTENT == 
        \/ \E n \in CORES: is_owner(n)
        \/ \A n \in CORES: cData[n] <= mData


\* All valid core/cache data are consistent
CORE_DATA_CONSISTENT == 
    \A o,k \in CORES: \/ ~is_I(o)
                      \/ /\ cData[o] >= mData
                         /\ cData[o] >= cData[k]

\* There is always at most one owner
AT_MOST_ONE_OWNER == 
    \A n,m \in CORES: \/ m = n
                      \/ ~is_owner(n)
                      \/ ~is_owner(m)
                       

IF_EXLUSIVE_REST_INV == 
    \/ ~\E n \in CORES: is_exclusive(n)
    \/  \A n \in CORES: \/ is_I(n) 
                        \/ is_exclusive(n)
                        
CONSISTENT_OWNER == 
    \A n \in CORES: \/ dOwner = EMPTY_OWNER
                    \/ dReqPending = 1
                    \/ cState[dOwner] = dState 

\* Directory correctly indicates owner and sharers
CONSISTENT_DIRECTORY_OWNER == 
    \A n \in CORES: \/ dOwner = n
                    \/ ~is_owner(n)

CONSISTENT_DIRECTORY_SHARERS == 
    \A k \in CORES: \/ is_I(k) 
                    \/ k \in dSharers

\* The owner and readers are always correctly reflected by any valid sharing vectors
INVARIANTS ==                           
    /\ MEM_DATA_CONSISTENT 
    /\ CORE_DATA_CONSISTENT 
    /\ AT_MOST_ONE_OWNER 
    /\ IF_EXLUSIVE_REST_INV 
    /\ CONSISTENT_OWNER 
    /\ CONSISTENT_DIRECTORY_OWNER 
    /\ CONSISTENT_DIRECTORY_SHARERS 


-------------------------------------------------------------------------------------
\* Helpers
dir_has_action_pending == dReqPending  = 1
dir_set_action_pending == dReqPending' = 1
dir_rst_action_pending == dReqPending' = 0

upd_dir_state(s) == dState' = s
upd_state(n, s)  == cState' = [cState EXCEPT![n] = s]

\* 
rmv_sharer(s) == dSharers' = dSharers \ {s}
add_sharer(s) == dSharers' = dSharers \union {s}


upd_owner(o) == 
    /\ dOwner'   = o  
    /\ dSharers' = {o}

rmv_owner(o) == 
    /\ rmv_sharer(o) 
    /\ dOwner' = EMPTY_OWNER
                
rst_acks(n) == 
    cRcvAcks' = [cRcvAcks EXCEPT![n] = {}]
add_ack(n, m) ==
    cRcvAcks' = [cRcvAcks EXCEPT![n] = cRcvAcks[n] \union {m.sender}]


rst_dir_acks == 
    dRcvAcks' = {}
add_dir_ack(m) == 
    dRcvAcks' = dRcvAcks \union {m.sender}

rcv_upd_ack_msg(n, m) == 
    /\ m.receiver = n
    /\ m.type = "UAck" 

rcv_ack_msg(n, m) == 
    /\ m.receiver = n
    /\ \/ m.type = "SAck" 
       \/ m.type = "SDataAck"


_is_last_Ack_from_set(n, m, set) == 
    set \subseteq (cRcvAcks[n] \union {m.sender})


is_last_Ack(n, m) == 
    /\ rcv_ack_msg(n, m)
    /\ _is_last_Ack_from_set(n, m, dSharers \ {n})

is_last_upd_Ack(n, m) == 
    /\ rcv_upd_ack_msg(n, m)
    /\ _is_last_Ack_from_set(n, m, CORES \ {n})

is_last_dir_Ack(m) == 
    /\ m.type = "UAck" 
    /\ dSharers \subseteq (dRcvAcks \union {m.sender})

owner_or_min_sharer == 
    IF dOwner # EMPTY_OWNER 
    THEN dOwner 
    ELSE Min(dSharers)

sharers_no_fwd == dSharers \ {owner_or_min_sharer}

-------------------------------------------------------------------------------------
\**********************************
\* Requests involving only Directory
\**********************************

\* Local write hit
EtoM(n) == \* E to M
    /\ cState[n] = "E"
    /\ upd_owner(n)
    /\ upd_state(n, "M")
    /\ upd_dir_state("M")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


\* Eviction
PutE(n) == \* E to I
    /\ cState[n] = "E"
    /\ rmv_owner(n)
    /\ upd_state(n, "I")
    /\ upd_dir_state("I")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


PutM(n) == \* M to I
    /\ cState[n] = "M"
    /\ rmv_owner(n)
    /\ upd_mem_data(n)
    /\ upd_state(n, "I")
    /\ upd_dir_state("I")
    /\ unchanged_gMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


PutS(n) == \* S to I/S
    /\ cState[n] = "S"
    /\ rmv_sharer(n)
    /\ upd_state(n, "I")
    /\ IF Cardinality(dSharers) = 1
       THEN upd_dir_state("I")
       ELSE upd_dir_state("S")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dOwner, dReqPending, cData, cRcvAcks, dRcvAcks>>


PutO(n) == \* O to I/S
    /\ cState[n] = "O"
    /\ rmv_owner(n)
    /\ upd_mem_data(n)
    /\ upd_state(n, "I")
    /\ IF Cardinality(dSharers) = 1
       THEN upd_dir_state("I")
       ELSE upd_dir_state("S")
    /\ unchanged_gMsgs 
    /\ UNCHANGED <<dReqPending, cData, cRcvAcks, dRcvAcks>>


\* Cache miss (fetching from memory)
GetS_dI(n) == \* I to E
    /\ dState = "I"
    /\ cState[n] = "I"
    /\ add_sharer(n)
    /\ rd_mem_data(n)
    /\ upd_state(n, "E")
    /\ upd_dir_state("E")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dOwner, dReqPending, cRcvAcks, dRcvAcks>>

GetM_dI(n) == \* I to M
    /\ dState = "I"
    /\ cState[n] = "I"
    /\ upd_owner(n)
    /\ rd_mem_data(n)
    /\ upd_state(n, "M")
    /\ upd_dir_state("M")
    /\ unchanged_gmMsgs 
    /\ UNCHANGED <<dReqPending, cRcvAcks, dRcvAcks>>
    
-------------------------------------------------------------------------------------
\* Dir
GetS_Fwd(n) ==
    /\ dState # "I"
    /\ cState[n] = "I"
    /\ dir_set_action_pending 
    /\ ucst_FwdGetS(n, owner_or_min_sharer)
    /\ IF (dState = "E" \/ dState = "S")
       THEN /\ upd_dir_state("S")
       ELSE upd_dir_state("O")   
    /\ unchanged_gmc
    /\ UNCHANGED <<dOwner, dSharers, dRcvAcks>>

GetS(n) ==
    \/ GetS_dI(n)
    \/ GetS_Fwd(n)

\* Sharers
RcvFwdGetS(n, m) ==
    /\ rcv_FwdGetS(m, n)
    /\ resp_SData(m)
    /\ IF (cState[n] = "E" \/ cState[n] = "S")
       THEN upd_state(n, "S")
       ELSE upd_state(n, "O")   
    /\ unchanged_gmd
    /\ UNCHANGED <<cData, cRcvAcks, dRcvAcks>>

\* Requester
RcvData(n, m) ==
    /\ rcv_SData(m, n)
    /\ deliver_Msg(m)
    /\ add_sharer(n)
    /\ upd_state(n, "S")
    /\ upd_core_data(n, m.data)
    /\ dir_rst_action_pending 
    /\ unchanged_gm
    /\ UNCHANGED <<dOwner, dState, cRcvAcks, dRcvAcks>>
    
-------------------------------------------------------------------------------------
\* Dir
GetM_Invs(n) ==
    /\ dState # "I"
    /\ cState[n] # "M"
    /\ cState[n] # "E"
    /\ Cardinality(dSharers \ {n}) > 0
    /\ rst_acks(n)
    /\ dir_set_action_pending 
    /\ upd_dir_state("M")
    /\ unchanged_m
    /\ UNCHANGED <<dOwner, dSharers, cState, cData, dRcvAcks>>
    /\ IF (dState = "E" \/ dState = "M")
       THEN /\ ucst_FwdGetM(n, owner_or_min_sharer)     \* single remote owner case
            /\ unchanged_g
       ELSE IF (dState = "S" \/ dOwner = n) 
            THEN /\ bcst_DInv(n, dSharers \ {n}) \* is owner but w/ sharers
                 /\ unchanged_Msgs
            ELSE /\ ucst_FwdGetM(n, owner_or_min_sharer) \* (remote) owner and sharers
                 /\ IF Cardinality(dSharers \ {owner_or_min_sharer, n}) > 0
                    THEN bcst_DInv(n, dSharers \ {owner_or_min_sharer, n})
                    ELSE unchanged_g

GetM(n) ==
    \/ EtoM(n) 
    \/ GetM_dI(n)
    \/ GetM_Invs(n)
      

\* Sharers -> rcvInv or FwdGetM
RcvInv(n, m) == 
    /\ (rcv_DInv(m, n) \/ rcv_FwdGetM(m, n))
    /\ upd_state(n, "I")
    /\ IF rcv_DInv(m, n)
           THEN resp_SAck(m)
           ELSE resp_SDataAck(m)
    /\ unchanged_gmd
    /\ UNCHANGED <<cData, cRcvAcks, dRcvAcks>>

\* Requester -> normal Ack or DataAck
RcvAck(n, m) == 
    /\ rcv_ack_msg(n, m)
    /\ deliver_Msg(m)
    /\ unchanged_gm
    /\ UNCHANGED <<dState, dRcvAcks>>
    /\ IF rcv_SDataAck(m, n)
       THEN upd_core_data(n, m.data)
       ELSE UNCHANGED <<cData>> 
    /\ IF ~is_last_Ack(n, m) 
       THEN /\ add_ack(n, m)
            /\ unchanged_d
            /\ UNCHANGED <<cState>>
       ELSE /\ rst_acks(n)
            /\ upd_owner(n)
            /\ upd_state(n, "M")
            /\ dir_rst_action_pending 

-------------------------------------------------------------------------------------
\* Dir
\*SharedUpdate

\*predicate
\* For simplicity now we always make every core a sharer here
MtoO(n) ==
    /\ dir_set_action_pending 
    /\ bcst_Upd(n, CORES \ {n}, cData[n])
    /\ unchanged_mMsgs 
    /\ IF ENABLE_DIR_ACKS 
       THEN /\ upd_state(n, "O") \* update eagerly to O state if dir collects ACKs
            /\ dRcvAcks = {n} \* add the requester to rcved acks for easier check of all acks predicate
       ELSE /\ rst_acks(n)
            /\ UNCHANGED <<cState, dRcvAcks>>
    /\ UNCHANGED <<cData, dOwner, dSharers, dState>>

RcvUpd(n, m) == 
    /\ rcv_Upd(m, n)
    /\ resp_UAck(m) 
    /\ upd_state(n, "S") 
    /\ upd_core_data(n, m.data)
    /\ unchanged_gmd
    /\ UNCHANGED <<cRcvAcks, dRcvAcks>>

RcvUpdAck(n, m) == 
    /\ ~ENABLE_DIR_ACKS 
    /\ cState[n] = "M"
    /\ rcv_upd_ack_msg(n, m)
    /\ deliver_Msg(m)
    /\ unchanged_gm
    /\ UNCHANGED <<cData, dRcvAcks>>
    /\ IF ~is_last_upd_Ack(n, m) 
       THEN /\ add_ack(n, m)
            /\ unchanged_d
            /\ UNCHANGED <<cState>>
       ELSE /\ rst_acks(n)
            /\ upd_state(n, "O")
            /\ dState'    = "O"
            /\ dOwner'    = n
            /\ dSharers'  = CORES
            /\ dir_rst_action_pending 


DirRcvUpdAck(m) == 
    /\ ENABLE_DIR_ACKS 
    /\ dir_has_action_pending 
    /\ dState = "M"
    /\ m.type = "UAck" 
    /\ deliver_Msg(m)
    /\ unchanged_gmc
    /\ UNCHANGED <<dOwner>>
    /\ IF ~is_last_dir_Ack(m)
       THEN /\ add_dir_ack(m) 
            /\ UNCHANGED <<dSharers, dReqPending, dState>>
       ELSE /\ rst_dir_acks
            /\ dState'    = "O"
            /\ dSharers'  = CORES
            /\ dir_rst_action_pending 

-------------------------------------------------------------------------------------
must_update(n) ==
    /\ cState[n] = "M"
    /\ cData[n]  = WRITE_TO_UPDATE


Requests(n) == 
    /\ ~dir_has_action_pending 
    /\ IF must_update(n)
       THEN MtoO(n)
       ELSE \/ GetM(n)
            \/ GetS(n)
            \/ PutE(n) 
            \/ PutM(n) 
            \/ PutS(n)
            \/ PutO(n)
       
SharerActions(n, m) == 
    \/ RcvUpd(n, m)
    \/ RcvInv(n, m)
    \/ RcvFwdGetS(n, m)

RequesterActions(n, m) == 
    \/ RcvAck(n, m)
    \/ RcvData(n, m)
    \/ RcvUpdAck(n, m)

DirActions(m) == DirRcvUpdAck(m)

MessageActions(n) ==
    \E m \in Msgs:
        \/ DirActions(m)
        \/ SharerActions(n, m)
        \/ RequesterActions(n, m)

PerformBcast ==
        /\ gBcstMsg # {}
        /\ \E m \in gBcstMsg:
           /\ _send_Msg(m)
           /\ unchanged_mcd
           /\ UNCHANGED <<dRcvAcks>>
           /\ IF gBcstMsgRcvers = {}
              THEN /\ gBcstMsg' = {} 
                   /\ UNCHANGED <<gBcstMsgRcvers>>
              ELSE LET rcver == CHOOSE x \in gBcstMsgRcvers : TRUE IN 
                   /\ gBcstMsg' = {[m EXCEPT!.receiver = rcver]}
                   /\ gBcstMsgRcvers' = gBcstMsgRcvers \ {rcver}
 
-------------------------------------------------------------------------------------
WriteData(n) == 
    /\ cState[n] = "M"
    /\ cData[n] < MAX_WRITES
    /\ ~must_update(n)
    /\ cData' = [cData EXCEPT![n] = cData[n] + 1]
    /\ unchanged_gdmMsgs 
    /\ UNCHANGED <<cState, cRcvAcks, dRcvAcks>>

\* Modeling 1-Update protocol (Directory, memory and core/cache actions)
Next == 
        IF   gBcstMsg # {}
        THEN PerformBcast 
        ELSE \E n \in CORES:
             \/ Requests(n) 
             \/ WriteData(n)
             \/ MessageActions(n)
(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

Invariants == /\ ([]ATypeOK) /\ ([]INVARIANTS)


THEOREM Spec => Invariants
=============================================================================