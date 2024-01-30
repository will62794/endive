(*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

\* 
\*  Original source: https://github.com/apache/zookeeper/blob/master/zookeeper-specifications/protocol-spec/Zab.tla
\*  Modifications by Will Schultz, Oct. 2023.
\* 

-------------------------------- MODULE Zab ---------------------------------
(* This is the formal specification for the Zab consensus algorithm,
   in DSN'2011, which represents protocol specification in our work.*)
EXTENDS Integers, FiniteSets, Sequences, Naturals, Apalache, TLC

\* The set of servers
CONSTANT 
    \* @typeAlias: SERVER = Str;
    \* @typeAlias: ZXID = <<Int,Int>>;
    \* @typeAlias: TXN = {zxid: ZXID, value: Int, ackSid: Set(SERVER), epoch: Int};
    \* @typeAlias: CEPOCHRECVTYPE = {sid: SERVER, connected: Bool, epoch: Int};
    \* @typeAlias: ACKERECVTYPE = {sid: SERVER, connected: Bool, peerLastEpoch: Int, peerHistory: Seq(TXN)};
    \* @typeAlias: ACKLDRECVTYPE = {sid: SERVER, connected: Bool};
    \* @type: Set(SERVER);
    Server

\* States of server
CONSTANTS 
    \* @type: Str;
    LOOKING, 
    \* @type: Str;
    FOLLOWING, 
    \* @type: Str;
    LEADING

\* Zab states of server
CONSTANTS 
    \* @type: Str;
    ELECTION, 
    \* @type: Str;
    DISCOVERY, 
    \* @type: Str;
    SYNCHRONIZATION, 
    \* @type: Str;
    BROADCAST

\* Message types
CONSTANTS 
    \* @type: Str;
    CEPOCH, 
    \* @type: Str;
    NEWEPOCH, 
    \* @type: Str;
    ACKEPOCH, 
    \* @type: Str;
    NEWLEADER, 
    \* @type: Str;  
    ACKLD, 
    \* @type: Str;
    COMMITLD, 
    \* @type: Str;
    PROPOSE, 
    \* @type: Str;
    ACK, 
    \* @type: Str;
    COMMIT

\* Variables that all servers use.
VARIABLES 
    \* State of server, in {LOOKING, FOLLOWING, LEADING}.
    \* @type: SERVER -> Str; 
    state,   
    \* Current phase of server, in
    \* {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}.      
    \* @type: SERVER -> Str; 
    zabState,   
    \* Epoch of the last LEADERINFO packet accepted, namely f.p in paper.    
    \* @type: SERVER -> Int; 
    acceptedEpoch, 
    \* Epoch of the last NEWLEADER packet accepted, namely f.a in paper. 
    \* @type: SERVER -> Int; 
    currentEpoch,   
    \* History of servers: sequence of transactions, containing: [zxid, value, ackSid, epoch].
    \* @type: SERVER -> Seq(TXN);                   
    history,       
    \* Maximum index and zxid known to be committed,
    \* namely 'lastCommitted' in Leader. Starts from 0,
    \* and increases monotonically before restarting. 
    \* @type: SERVER -> {index: Int, zxid: ZXID};
    lastCommitted   

\* Variables only used for leader.
VARIABLES 
    \* Set of servers leader connects.
    \* @type: SERVER -> Set(SERVER);
    learners,   
    \* Set of learners leader has received CEPOCH from.
    \* Set of record [sid, connected, epoch],
    \* where epoch means f.p from followers.    
    \* @type: SERVER -> Set(CEPOCHRECVTYPE);
    cepochRecv,  
    \* Set of learners leader has received ACKEPOCH from.
    \* Set of record  [sid, connected, peerLastEpoch, peerHistory], to record f.a and h(f) from followers.   
    \* @type: SERVER -> Set(ACKERECVTYPE);
    ackeRecv,  
    \* Set of learners leader has received ACKLD from.
    \* Set of record [sid, connected].     
    \* @type: SERVER -> Set({sid: SERVER, connected: Bool});
    ackldRecv,   
    \* Count of txns leader has broadcast.   
    \* @type: SERVER -> Int;
    sendCounter     

\* Variables only used for follower.
VARIABLES 
    \* If follower has connected with leader.
    \* If follower lost connection, then null.
    \* @type: SERVER -> SERVER;
    connectInfo 

\* Variable representing oracle of leader.
VARIABLE  
    \* Current oracle.
    \* @type: SERVER;
    leaderOracle  

\* Variables about network channel.
\* Simulates network channel.
\* msgs[i][j] means the input buffer of server j from server i.

VARIABLE 
    \* @type: SERVER -> (SERVER -> Seq(Int));
    mesgs

VARIABLE 
    \* @type: Set({ mtype: Str, mepoch: Int, msrc: SERVER, mdst: SERVER, morder: Int });
    CEPOCHmsgs

VARIABLE
    \* @type: Set ({ mtype: Str, mepoch: Int, msrc: SERVER, mdst: SERVER, morder: Int });
    NEWEPOCHmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mepoch: Int, mhistory: Seq({zxid: <<Int,Int>>, value: Int, ackSid: Set(SERVER), epoch: Int}), msrc: SERVER, mdst: SERVER, morder: Int });
    ACKEPOCHmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mepoch: Int, mhistory: Seq({zxid: <<Int,Int>>, value: Int, ackSid: Set(SERVER), epoch: Int}), msrc: SERVER, mdst: SERVER, morder: Int });
    NEWLEADERmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER, morder: Int });
    ACKLDmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER, morder: Int });
    COMMITLDmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mzxid: ZXID, mdata: Int, msrc: SERVER, mdst: SERVER });
    PROPOSEmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER});
    ACKmsgs

VARIABLE 
    \* @type: Set ({ mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER});
    COMMITmsgs

NullPoint == "Null"
Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}

serverVars == <<state, zabState, acceptedEpoch, currentEpoch, history, lastCommitted>>

leaderVars == <<learners, cepochRecv, ackeRecv, ackldRecv, sendCounter>>

followerVars == connectInfo

electionVars == leaderOracle

msgVars == <<mesgs, CEPOCHmsgs, NEWEPOCHmsgs, ACKEPOCHmsgs, NEWLEADERmsgs, ACKLDmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

vars == <<serverVars, leaderVars, followerVars, electionVars, msgVars>>

\* Gives a candidate TypeOK definition for all variables in the spec.
\* TypeOK == 
\*     /\ state \in [Server -> {LOOKING, FOLLOWING, LEADING}]
\*     /\ zabState \in [Server -> {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}]
\*     /\ acceptedEpoch \in [Server -> Nat]
\*     /\ currentEpoch \in [Server -> Nat]
\*     /\ history \in [Server -> Seq([zxid: Nat, value: Nat, ackSid: Server, epoch: Nat])]
\*     /\ lastCommitted \in [Server -> [index: Nat, zxid: Nat \X Nat]]
\*     /\ learners \in [Server -> SUBSET Server]
\*     /\ cepochRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN, epoch: Nat]]
\*     /\ ackeRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: Seq([zxid: Nat, value: Nat, ackSid: Server, epoch: Nat])]]
\*     /\ ackldRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN]]
\*     /\ sendCounter \in [Server -> Nat]
\*     /\ connectInfo \in [Server -> Server]
\*     /\ leaderOracle \in Server
\*     /\ msgs = {}
    \* /\ msgs \in [Server -> [Server -> Seq([mtype: {CEPOCH, NEWEPOCH, ACKEPOCH, NEWLEADER, ACKLD, COMMITLD, PROPOSE, ACK, COMMIT}, 
                                            \* mepoch: Nat, 

CONSTANT 
    \* @type: Int;
    MaxEpoch
CONSTANT 
    \* @type: Int;
    MaxHistLen

Epoch == 1..MaxEpoch
Value == Nat

-----------------------------------------------------------------------------
\* Return the maximum value from the set S
Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n >= m
\* Return the minimum value from the set S
Minimum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S: \A m \in S: n <= m

\* Check server state                       
IsLeader(s)   == state[s] = LEADING
IsFollower(s) == state[s] = FOLLOWING
IsLooking(s)  == state[s] = LOOKING

\* Check if s is a quorum
IsQuorum(s) == s \in Quorums

IsMyLearner(i, j) == j \in learners[i]
IsMyLeader(i, j)  == connectInfo[i] = j
HasNoLeader(i)    == connectInfo[i] = NullPoint
HasLeader(i)      == connectInfo[i] /= NullPoint
-----------------------------------------------------------------------------
\* FALSE: zxid1 <= zxid2; TRUE: zxid1 > zxid2
\* @type: (ZXID, ZXID) => Bool;
ZxidCompare(zxid1, zxid2) == \/ zxid1[1] > zxid2[1]
                             \/ /\ zxid1[1] = zxid2[1]
                                /\ zxid1[2] > zxid2[2]

\* @type: (ZXID, ZXID) => Bool;
ZxidEqual(zxid1, zxid2) == zxid1[1] = zxid2[1] /\ zxid1[2] = zxid2[2]

\* @type: (TXN, ZXID) => Bool;
TxnZxidEqual(txn, z) == txn.zxid[1] = z[1] /\ txn.zxid[2] = z[2]

\* @type: (TXN, TXN) => Bool;
TxnEqual(txn1, txn2) == /\ ZxidEqual(txn1.zxid, txn2.zxid)
                        /\ txn1.value = txn2.value

\* @type: (TXN, TXN) => Bool;
EpochPrecedeInTxn(txn1, txn2) == txn1.zxid[1] < txn2.zxid[1]
-----------------------------------------------------------------------------
\* Actions about recorder
\* GetParameter(p) == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE 0
\* GetRecorder(p)  == IF p \in DOMAIN recorder   THEN recorder[p]   ELSE 0

\* RecorderGetHelper(m) == (m :> recorder[m])
\* RecorderIncHelper(m) == (m :> recorder[m] + 1)

\* RecorderIncTimeout == RecorderIncHelper("nTimeout")
\* RecorderGetTimeout == RecorderGetHelper("nTimeout")
\* RecorderIncRestart == RecorderIncHelper("nRestart")
\* RecorderGetRestart == RecorderGetHelper("nRestart")
\* RecorderSetTransactionNum(pc) == ("nTransaction" :> 
\*                                 IF pc[1] = "LeaderProcessRequest" THEN
\*                                     LET s == CHOOSE i \in Server: 
\*                                         \A j \in Server: Len(history'[i]) >= Len(history'[j])                       
\*                                     IN Len(history'[s])
\*                                 ELSE recorder["nTransaction"])
\* RecorderSetMaxEpoch(pc)       == ("maxEpoch" :> 
\*                                 IF pc[1] = "LeaderProcessCEPOCH" THEN
\*                                     LET s == CHOOSE i \in Server:
\*                                         \A j \in Server: acceptedEpoch'[i] >= acceptedEpoch'[j]
\*                                     IN acceptedEpoch'[s]
\*                                 ELSE recorder["maxEpoch"])
\* RecorderSetRequests(pc)       == ("nClientRequest" :>
\*                                 IF pc[1] = "LeaderProcessRequest" THEN
\*                                     recorder["nClientRequest"] + 1
\*                                 ELSE recorder["nClientRequest"] )
\* RecorderSetPc(pc)      == ("pc" :> pc)
\* RecorderSetFailure(pc) == (m :> 0)
    
    \* CASE pc[1] = "Timeout"         -> RecorderIncTimeout @@ RecorderGetRestart
    \*                       []   pc[1] = "LeaderTimeout"   -> RecorderIncTimeout @@ RecorderGetRestart
    \*                       []   pc[1] = "FollowerTimeout" -> RecorderIncTimeout @@ RecorderGetRestart
    \*                       []   pc[1] = "Restart"         -> RecorderIncTimeout @@ RecorderIncRestart
    \*                       []   OTHER                     -> RecorderGetTimeout @@ RecorderGetRestart

UpdateRecorder(pc) == TRUE \*recorder' = recorder 
\* RecorderSetFailure(pc)      @@ RecorderSetTransactionNum(pc)
\*                                   @@ RecorderSetMaxEpoch(pc)  @@ RecorderSetPc(pc) 
\*                                   @@ RecorderSetRequests(pc)  @@ recorder

\* UnchangeRecorder   == UNCHANGED recorder

\* CheckParameterHelper(n, p, Comp(_,_)) == IF p \in DOMAIN Parameters 
\*                                          THEN Comp(n, Parameters[p])
\*                                          ELSE TRUE
\* CheckParameterLimit(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

\* CheckTimeout        == CheckParameterLimit(recorder.nTimeout,     "MaxTimeoutFailures")
\* CheckTransactionNum == CheckParameterLimit(recorder.nTransaction, "MaxTransactionNum")
\* CheckEpoch          == CheckParameterLimit(recorder.maxEpoch,     "MaxEpoch")
\* CheckRestart        == /\ CheckTimeout 
\*                        /\ CheckParameterLimit(recorder.nRestart,  "MaxRestarts")

\* CheckStateConstraints == CheckTimeout /\ CheckTransactionNum /\ CheckEpoch /\ CheckRestart
-----------------------------------------------------------------------------
\* Actions about network
\* @type: (SERVER, SERVER) => Bool;
\* PendingCEPOCH(i, j)    == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = CEPOCH
\* PendingNEWEPOCH(i, j)  == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = NEWEPOCH
\* PendingACKEPOCH(i, j)  == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = ACKEPOCH
\* PendingNEWLEADER(i, j) == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = NEWLEADER
\* PendingACKLD(i, j)     == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = ACKLD
\* PendingCOMMITLD(i, j)  == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = COMMITLD
\* PendingPROPOSE(i, j)   == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = PROPOSE
\* PendingACK(i, j)       == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = ACK
\* PendingCOMMIT(i, j)    == /\ msgs[j][i] /= << >>
\*                           /\ msgs[j][i][1].mtype = COMMIT

PendingCEPOCH(i, j)    == TRUE
PendingNEWEPOCH(i, j)  == TRUE
PendingACKEPOCH(i, j)  == TRUE
PendingNEWLEADER(i, j) == TRUE
PendingACKLD(i, j)     == TRUE
PendingCOMMITLD(i, j)  == TRUE
PendingPROPOSE(i, j)   == TRUE
PendingACK(i, j)       == TRUE
PendingCOMMIT(i, j)    == TRUE
\* Add a message to msgs - add a message m to msgs.
\* Send(i, j, m) == msgs' = [msgs EXCEPT ![i][j] = Append(msgs[i][j], m)]
\* SendIn(ms, i, j, m) == ms' = [ms EXCEPT ![i][j] = Append(ms[i][j], m)]
\* Remove a message from msgs - discard head of msgs.
\* Discard(i, j) == msgs' = IF msgs[i][j] /= << >> THEN [msgs EXCEPT ![i][j] = Tail(msgs[i][j])] ELSE msgs
\* DiscardIn(ms, i, j) == ms' = IF ms[i][j] /= << >> THEN [ms EXCEPT ![i][j] = Tail(ms[i][j])] ELSE ms
\* Combination of Send and Discard - discard head of msgs[j][i] and add m into msgs.
\* Reply(i, j, m) == msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m)]
\* ReplyIn(ms, i, j, m) == ms' = [ms EXCEPT ![j][i] = Tail(ms[j][i]),
                                    \*    ![i][j] = Append(ms[i][j], m)]

\* @type: Seq(TXN) => ZXID;
LastZxidOfHistory(his) == IF Len(his) = 0 THEN <<0, 0>> ELSE his[Len(his)].zxid
\* @type: SERVER => ZXID;
LastZxid(i) == LastZxidOfHistory(history[i])


MaxWithZero(S) == IF S = {} THEN 0 ELSE CHOOSE n \in S: \A m \in S: n >= m
MinWithZero(S) == IF S = {} THEN 0 ELSE CHOOSE n \in S: \A m \in S: n >= m

\* The highest message order counter among all messages sent between i and j, plus 1. 
NextMsgOrderCEPOCH(i,j) == MaxWithZero({c.morder : c \in {m \in CEPOCHmsgs : m.msrc = i /\ m.mdst = j}})
NextMsgOrderNEWEPOCH(i,j) == MaxWithZero({c.morder : c \in {m \in ACKEPOCHmsgs : m.msrc = i /\ m.mdst = j}})
NextMsgOrderACKEPOCH(i,j) == MaxWithZero({c.morder : c \in {m \in ACKEPOCHmsgs : m.msrc = i /\ m.mdst = j}})
NextMsgOrderNEWLEADER(i,j) == MaxWithZero({c.morder : c \in {m \in NEWLEADERmsgs : m.msrc = i /\ m.mdst = j}})
NextMsgOrderACKLD(i,j) == MaxWithZero({c.morder : c \in {m \in ACKLDmsgs : m.msrc = i /\ m.mdst = j}})
NextMsgOrderCOMMITLD(i,j) == MaxWithZero({c.morder : c \in {m \in COMMITLDmsgs : m.msrc = i /\ m.mdst = j}})
\* NextMsgOrderPROPOSE(i,j) == MaxWithZero({c.morder : c \in {m \in PROPOSEmsgs : m.msrc = i /\ m.mdst = j}})
\* NextMsgOrderACK(i,j) == MaxWithZero({c.morder : c \in {m \in ACKmsgs : m.msrc = i /\ m.mdst = j}})
\* NextMsgOrderCOMMIT(i,j) == MaxWithZero({c.morder : c \in {m \in COMMITmsgs : m.msrc = i /\ m.mdst = j}})

MinMsgOrderCEPOCH(i,j) == MinWithZero({c.morder : c \in {m \in CEPOCHmsgs : m.msrc = i /\ m.mdst = j}})
MinMsgOrderNEWEPOCH(i,j) == MinWithZero({c.morder : c \in {m \in ACKEPOCHmsgs : m.msrc = i /\ m.mdst = j}})
MinMsgOrderACKEPOCH(i,j) == MinWithZero({c.morder : c \in {m \in ACKEPOCHmsgs : m.msrc = i /\ m.mdst = j}})
MinMsgOrderNEWLEADER(i,j) == MinWithZero({c.morder : c \in {m \in NEWLEADERmsgs : m.msrc = i /\ m.mdst = j}})
MinMsgOrderACKLD(i,j) == MinWithZero({c.morder : c \in {m \in ACKLDmsgs : m.msrc = i /\ m.mdst = j}})
MinMsgOrderCOMMITLD(i,j) == MinWithZero({c.morder : c \in {m \in COMMITLDmsgs : m.msrc = i /\ m.mdst = j}})
\* MinMsgOrderPROPOSE(i,j) == MinWithZero({c.morder : c \in {m \in PROPOSEmsgs : m.msrc = i /\ m.mdst = j}})
\* MinMsgOrderACK(i,j) == MinWithZero({c.morder : c \in {m \in ACKmsgs : m.msrc = i /\ m.mdst = j}})
\* MinMsgOrderCOMMIT(i,j) == MinWithZero({c.morder : c \in {m \in COMMITmsgs : m.msrc = i /\ m.mdst = j}})

\* Maximum({
\*     NextMsgOrderCEPOCH, 
\*     NextMsgOrderNEWEPOCH,
\*     NextMsgOrderACKEPOCH,
\*     NextMsgOrderNEWLEADER,
\*     NextMsgOrderACKLD,
\*     NextMsgOrderCOMMITLD,
\*     NextMsgOrderPROPOSE,
\*     NextMsgOrderACK,
\*     NextMsgOrderCOMMIT
\* })

\* \cup NEWEPOCHmsgs \cup ACKEPOCHmsgs \cup NEWLEADERmsgs \cup ACKLDmsgs \cup COMMITLDmsgs \cup PROPOSEmsgs \cup ACKmsgs \cup COMMITmsgs
\* MsgsFrom(i,j) == {m \in }
NextMsgOrder(i,j) == 0
    \* Disable for now.
    \* Maximum({
    \*     NextMsgOrderCEPOCH(i,j), 
    \*     NextMsgOrderNEWEPOCH(i,j),
    \*     NextMsgOrderACKEPOCH(i,j),
    \*     NextMsgOrderNEWLEADER(i,j),
    \*     NextMsgOrderACKLD(i,j),
    \*     NextMsgOrderCOMMITLD(i,j),
    \*     NextMsgOrderPROPOSE(i,j),
    \*     NextMsgOrderACK(i,j),
    \*     NextMsgOrderCOMMIT(i,j)
    \* }) + 1

MinMsgOrder(i,j) ==
    MinWithZero({
        MinMsgOrderCEPOCH(i,j), 
        MinMsgOrderNEWEPOCH(i,j),
        MinMsgOrderACKEPOCH(i,j),
        MinMsgOrderNEWLEADER(i,j),
        MinMsgOrderACKLD(i,j),
        MinMsgOrderCOMMITLD(i,j)
        \* MinMsgOrderPROPOSE(i,j),
        \* MinMsgOrderACK(i,j),
        \* MinMsgOrderCOMMIT(i,j)
    })



\* Shuffle input buffer.
\* 
\* Clean(i, j) == 
\*     \* /\ msgs' = [msgs EXCEPT ![j][i] = << >>, ![i][j] = << >>]   
\*     \* Remove all messages between i and j.
\*     /\ CEPOCHmsgs' = {m \in CEPOCHmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ NEWEPOCHmsgs' = {m \in NEWEPOCHmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ ACKEPOCHmsgs' = {m \in ACKEPOCHmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ NEWLEADERmsgs' = {m \in NEWLEADERmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ ACKLDmsgs' = {m \in ACKLDmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ COMMITLDmsgs' = {m \in COMMITLDmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ PROPOSEmsgs' = {m \in PROPOSEmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ ACKmsgs' = {m \in ACKmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}
\*     /\ COMMITmsgs' = {m \in COMMITmsgs : <<m.msrc,m.mdst>> \notin {<<i,j>>, <<j,i>>}}

\* CleanInputBuffer(S) == 
\*     /\ msgs' = [s \in Server |-> [v \in Server |-> IF v \in S THEN << >> ELSE msgs[s][v] ] ]
\* Leader broadcasts a message PROPOSE to all other servers in Q.
\* Note: In paper, Q is fuzzy. We think servers who leader broadcasts NEWLEADER to
\*       should receive every PROPOSE. So we consider ackeRecv as Q.
\* Since we let ackeRecv = Q, there may exist some follower receiving COMMIT before
\* COMMITLD, and zxid in COMMIT later than zxid in COMMITLD. To avoid this situation,
\* if f \in ackeRecv but \notin ackldRecv, f should not receive COMMIT until 
\* f \in ackldRecv and receives COMMITLD.
\* Broadcast(i, m) ==
\*         LET ackeRecv_quorum == {a \in ackeRecv[i]: a.connected = TRUE }
\*             sid_ackeRecv == { a.sid: a \in ackeRecv_quorum }
\*         IN msgs' = [msgs EXCEPT ![i] = [v \in Server |-> IF /\ v \in sid_ackeRecv
\*                                                             /\ v \in learners[i] 
\*                                                             /\ v /= i
\*                                                          THEN Append(msgs[i][v], m)
\*                                                          ELSE msgs[i][v] ] ] 
\* Since leader decides to broadcasts message COMMIT when processing ACK, so
\* we need to discard ACK and broadcast COMMIT.
\* Here Q is ackldRecv, because we assume that f should not receive COMMIT until
\* f receives COMMITLD.
\* DiscardAndBroadcast(i, j, m) ==
\*         LET ackldRecv_quorum == {a \in ackldRecv[i]: a.connected = TRUE }
\*             sid_ackldRecv == { a.sid: a \in ackldRecv_quorum }
\*         IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
\*                                 ![i] = [v \in Server |-> IF /\ v \in sid_ackldRecv
\*                                                             /\ v \in learners[i] 
\*                                                             /\ v /= i
\*                                                          THEN Append(msgs[i][v], m)
\*                                                          ELSE msgs[i][v] ] ]  
\* Leader broadcasts LEADERINFO to all other servers in cepochRecv.
DiscardAndBroadcastNEWEPOCH(i, j, m) ==
        LET new_cepochRecv_quorum == {c \in cepochRecv'[i]: c.connected = TRUE }
            new_sid_cepochRecv == { c.sid: c \in new_cepochRecv_quorum }
        IN /\ mesgs' = mesgs
        \* [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
        \*                         ![i] = [v \in Server |-> IF /\ v \in new_sid_cepochRecv
        \*                                                     /\ v \in learners[i] 
        \*                                                     /\ v /= i
        \*                                                  THEN Append(msgs[i][v], m)
        \*                                                  ELSE msgs[i][v] ] ]
           /\ NEWEPOCHmsgs' = NEWEPOCHmsgs \cup {[ mtype  |-> NEWEPOCH,
                                                   mepoch |-> acceptedEpoch'[i],
                                                   msrc |-> i, mdst |-> to, 
                                                   morder |-> NextMsgOrder(i,to) ] : to \in (new_sid_cepochRecv \cap learners[i]) \ {i}}

\* Leader broadcasts NEWLEADER to all other servers in ackeRecv.
DiscardAndBroadcastNEWLEADER(i, j, m, toSend) ==
        LET new_ackeRecv_quorum == {a \in ackeRecv'[i]: a.connected = TRUE }
            new_sid_ackeRecv == { a.sid: a \in new_ackeRecv_quorum } IN
           /\ mesgs' = mesgs
        \*    [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                \* ![i] = [v \in Server |-> IF /\ v \in new_sid_ackeRecv
                                                            \* /\ v \in learners[i] 
                                                            \* /\ v /= i
                                                        \*  THEN Append(msgs[i][v], m)
                                                        \*  ELSE msgs[i][v] ] ]
           /\ NEWLEADERmsgs' = NEWLEADERmsgs \cup {[ mtype  |-> NEWLEADER,
                                                   mepoch |-> acceptedEpoch[i],
                                                   mhistory |-> toSend,
                                                   msrc |-> i, mdst |-> to, morder |-> NextMsgOrder(i,to) ] : to \in (new_sid_ackeRecv \cap learners[i]) \ {i}} 
\* Leader broadcasts COMMITLD to all other servers in ackldRecv.
DiscardAndBroadcastCOMMITLD(i, j, m) ==
        LET new_ackldRecv_quorum == {a \in ackldRecv'[i]: a.connected = TRUE }
            new_sid_ackldRecv == { a.sid: a \in new_ackldRecv_quorum }
        IN 
         /\ mesgs' = mesgs
        \*  [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
        \*                         ![i] = [v \in Server |-> IF /\ v \in new_sid_ackldRecv
        \*                                                     /\ v \in learners[i] 
        \*                                                     /\ v /= i
        \*                                                  THEN Append(msgs[i][v], m)
        \*                                                  ELSE msgs[i][v] ] ]
         /\ COMMITLDmsgs' = COMMITLDmsgs \cup {
                [   mtype |-> COMMITLD, 
                    mzxid |-> LastZxid(i),
                    msrc |-> i, mdst |-> to, morder |-> 0 ] : to \in (new_sid_ackldRecv \cap learners[i]) \ {i}} 
-----------------------------------------------------------------------------
\* Define initial values for all variables 
InitServerVars == /\ state         = [s \in Server |-> LOOKING]
                  /\ zabState      = [s \in Server |-> ELECTION]
                  /\ acceptedEpoch = [s \in Server |-> 0]
                  /\ currentEpoch  = [s \in Server |-> 0]
                  /\ history       = [s \in Server |-> << >>]
                  /\ lastCommitted = [s \in Server |-> [ index |-> 0,
                                                         zxid  |-> <<0, 0>> ] ]

InitLeaderVars == /\ learners       = [s \in Server |-> {}]
                  /\ cepochRecv     = [s \in Server |-> {}]
                  /\ ackeRecv       = [s \in Server |-> {}]
                  /\ ackldRecv      = [s \in Server |-> {}]
                  /\ sendCounter    = [s \in Server |-> 0]

InitFollowerVars == connectInfo = [s \in Server |-> NullPoint]

InitElectionVars == leaderOracle = NullPoint

InitMsgVars == 
    /\ mesgs = [s \in Server |-> [v \in Server |-> << >>] ]
    /\ CEPOCHmsgs   = {}
    /\ NEWEPOCHmsgs = {}
    /\ ACKEPOCHmsgs = {}
    /\ NEWLEADERmsgs = {}
    /\ ACKLDmsgs    = {}
    /\ COMMITLDmsgs = {}
    /\ PROPOSEmsgs  = {}
    /\ ACKmsgs      = {}
    /\ COMMITmsgs   = {}

Init == /\ InitServerVars
        /\ InitLeaderVars
        /\ InitFollowerVars
        /\ InitElectionVars
        \* /\ InitVerifyVars
        /\ InitMsgVars

-----------------------------------------------------------------------------
\* Utils in state switching
FollowerShutdown(i) == 
        /\ state'    = [state      EXCEPT ![i] = LOOKING]
        /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
        /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]

\* LeaderShutdown(i) ==
\*         /\ LET S == learners[i]
\*            IN /\ state' = [s \in Server |-> IF s \in S THEN LOOKING ELSE state[s] ]
\*               /\ zabState' = [s \in Server |-> IF s \in S THEN ELECTION ELSE zabState[s] ]
\*               /\ connectInfo' = [s \in Server |-> IF s \in S THEN NullPoint ELSE connectInfo[s] ]
\*               /\ CleanInputBuffer(S)
\*         /\ learners'   = [learners   EXCEPT ![i] = {}]

SwitchToFollower(i) ==
        /\ state' = [state EXCEPT ![i] = FOLLOWING]
        /\ zabState' = [zabState EXCEPT ![i] = DISCOVERY]

SwitchToLeader(i) ==
        /\ state' = [state EXCEPT ![i] = LEADING]
        /\ zabState' = [zabState EXCEPT ![i] = DISCOVERY]
        /\ learners' = [learners EXCEPT ![i] = {i}]
        /\ cepochRecv' = [cepochRecv EXCEPT ![i] = { [ sid       |-> i,
                                                       connected |-> TRUE,
                                                       epoch     |-> acceptedEpoch[i] ] }]
        /\ ackeRecv' = [ackeRecv EXCEPT ![i] = { [ sid           |-> i,
                                                   connected     |-> TRUE,
                                                   peerLastEpoch |-> currentEpoch[i],
                                                   peerHistory   |-> history[i] ] }]
        /\ ackldRecv' = [ackldRecv EXCEPT ![i] = { [ sid       |-> i,
                                                     connected |-> TRUE ] }]
        /\ sendCounter' = [sendCounter EXCEPT ![i] = 0]

\* @type: (Set(CEPOCHRECVTYPE), SERVER) => Set(CEPOCHRECVTYPE);
RemoveCepochRecv(set, sid) ==
    IF sid \notin {s.sid: s \in set} 
        THEN set
        ELSE LET info == CHOOSE s \in set: s.sid = sid
                 new_info == [ sid       |-> sid,
                               connected |-> FALSE,
                               epoch     |-> info.epoch ]
            IN (set \ {info}) \union {new_info}

\* @type: (Set(ACKERECVTYPE), SERVER) => Set(ACKERECVTYPE);
RemoveAckeRecv(set, sid) ==
        IF sid \notin {s.sid: s \in set} THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid |-> sid,
                                  connected |-> FALSE,
                                  peerLastEpoch |-> info.peerLastEpoch,
                                  peerHistory   |-> info.peerHistory ]
                IN (set \ {info}) \union {new_info}

\* @type: (Set(ACKLDRECVTYPE), SERVER) => Set(ACKLDRECVTYPE);
RemoveAckldRecv(set, sid) ==
        IF sid \notin {s.sid: s \in set} THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid |-> sid,
                                  connected |-> FALSE ]
                IN (set \ {info}) \union {new_info}

\* RemoveLearner(i, j) ==
        \* /\ learners'   = [learners   EXCEPT ![i] = @ \ {j}] 
        \* /\ cepochRecv' = [cepochRecv EXCEPT ![i] = RemoveCepochRecv(cepochRecv[i], j) ]
        \* /\ ackeRecv'   = [ackeRecv   EXCEPT ![i] = RemoveAckeRecv(ackeRecv[i], j) ]
        \* /\ ackldRecv'  = [ackldRecv  EXCEPT ![i] = RemoveAckldRecv(ackldRecv[i], j) ]
-----------------------------------------------------------------------------
\* Actions of election
UpdateLeader(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= i
        /\ leaderOracle' = i
        /\ SwitchToLeader(i)
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, followerVars, msgVars>>


FollowLeaderMyself(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= NullPoint
        /\ leaderOracle = i
        /\ SwitchToLeader(i)
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, electionVars, followerVars, msgVars>>

FollowLeaderOther(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= NullPoint
        /\ leaderOracle /= i
        /\ SwitchToFollower(i)
        /\ UNCHANGED <<leaderVars, acceptedEpoch, currentEpoch, history, lastCommitted, electionVars, followerVars, msgVars>>

-----------------------------------------------------------------------------
(* Actions of situation error. Situation error in protocol spec is different
   from latter specs. This is for compressing state space, we focus on results
   from external events (e.g. network partition, node failure, etc.), so we do
   not need to add variables and actions about network conditions and node 
   conditions. It is reasonable that we have action 'Restart' but no 'Crash',
   because when a node does not execute any internal events after restarting, 
   this is equivalent to executing a crash.
*)

\* \* \* Timeout between leader and follower.  
\* TimeoutWithQuorum(i, j) ==
\*     /\ IsLeader(i)   
\*     /\ IsMyLearner(i, j)
\*     /\ IsFollower(j) 
\*     /\ IsMyLeader(j, i)
\*     /\ (learners[i] \ {j}) \in Quorums  \* just remove this learner
\*     /\ state' = [s \in Server |-> IF s \in learners[i] THEN LOOKING ELSE state[s] ]
\*     /\ zabState' = [s \in Server |-> IF s \in learners[i] THEN ELECTION ELSE zabState[s] ]
\*     /\ connectInfo' = [s \in Server |-> IF s \in learners[i] THEN NullPoint ELSE connectInfo[s] ]
\*     /\ learners'   = [learners   EXCEPT ![i] = {}]
\*     \* /\ FollowerShutdown(j)
\*     /\ state'    = [state      EXCEPT ![i] = LOOKING]
\*     /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
\*     /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]
\*     \* /\ Clean(i, j)
\*     /\ COMMITmsgs' = {m \in COMMITmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ CEPOCHmsgs' = {m \in CEPOCHmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ NEWEPOCHmsgs' = {m \in NEWEPOCHmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ ACKEPOCHmsgs' = {m \in ACKEPOCHmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ NEWLEADERmsgs' = {m \in NEWLEADERmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ ACKLDmsgs' = {m \in ACKLDmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ COMMITLDmsgs' = {m \in COMMITLDmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ PROPOSEmsgs' = {m \in PROPOSEmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ ACKmsgs' = {m \in ACKmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ COMMITmsgs' = {m \in COMMITmsgs : ~((m.msrc = i /\ m.mdst = j) \/ (m.msrc = j /\ m.mdst = i))}
\*     /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, sendCounter, electionVars>>

TimeoutNoQuorum(i, j) ==
        \* /\ CheckTimeout \* test restrictions of timeout
        /\ IsLeader(i)   
        /\ IsMyLearner(i, j)
        /\ IsFollower(j) 
        /\ IsMyLeader(j, i)
        /\ (learners[i] \ {j}) \notin Quorums \* leader switches to looking
        \* /\ CleanInputBuffer(learners[i])
        /\ COMMITmsgs' = {} \*{m \in COMMITmsgs : ~(m["mdst"] \in learners[i])} 
        \* \cup {[mtype |-> COMMIT, mzxid |-> <<2, 0>>, msrc |-> "s5", mdst |-> "s6"]}
        \* /\ COMMITmsgs' = {} \* {m \in COMMITmsgs : ~(m.mdst \in learners[i])}
        /\ CEPOCHmsgs' = {} \* {m \in CEPOCHmsgs : m.mdst \notin learners[i]}
        /\ NEWEPOCHmsgs' = {} \* {m \in NEWEPOCHmsgs : m.mdst \notin learners[i]}
        /\ ACKEPOCHmsgs' = {} \* {m \in ACKEPOCHmsgs : m.mdst \notin learners[i]}
        /\ NEWLEADERmsgs' = {} \* {m \in NEWLEADERmsgs : m.mdst \notin learners[i]}
        /\ ACKLDmsgs' = {} \* {m \in ACKLDmsgs : m.mdst \notin learners[i]}
        /\ COMMITLDmsgs' = {} \* {m \in COMMITLDmsgs : m.mdst \notin learners[i]}
        /\ PROPOSEmsgs' = {} \* {m \in PROPOSEmsgs : ~(m.mdst \in learners[i])}
        /\ ACKmsgs' = {} \* {m \in ACKmsgs : ~(m.mdst \in learners[i])}
        \* /\ PrintT("-----------------")
        \* /\ PrintT(i)
        \* /\ PrintT(PROPOSEmsgs)
        \* /\ PrintT(learners[i])
        \* /\ PrintT({m \in PROPOSEmsgs : ~(m.mdst \in learners[i])})
        \* /\ COMMITmsgs' = {m \in COMMITmsgs : m.mdst \notin learners[i]}
        /\ state' = [s \in Server |-> IF s \in learners[i] THEN LOOKING ELSE state[s] ]
        /\ zabState' = [s \in Server |-> IF s \in learners[i] THEN ELECTION ELSE zabState[s] ]
        /\ connectInfo' = [s \in Server |-> IF s \in learners[i] THEN NullPoint ELSE connectInfo[s] ]
        /\ learners'   = [learners   EXCEPT ![i] = {}]
        /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv, acceptedEpoch, currentEpoch, history, lastCommitted, sendCounter, electionVars, mesgs>>

\* Restart(i) ==
\*         \* /\ CheckRestart \* test restrictions of restart
\*         /\ \/ /\ IsLooking(i)
\*               /\ UNCHANGED <<state, zabState, learners, followerVars, msgVars,
\*                     cepochRecv, ackeRecv, ackldRecv>>
\*            \/ /\ IsFollower(i)
\*               /\ LET connectedWithLeader == HasLeader(i)
\*                  IN \/ /\ connectedWithLeader
\*                        /\ LET leader == connectInfo[i]
\*                               newLearners == learners[leader] \ {i}
\*                           IN 
\*                           \/ /\ IsQuorum(newLearners)  \* leader remove learner i
\*                              /\ RemoveLearner(leader, i)
\*                              /\ FollowerShutdown(i)
\*                              /\ Clean(leader, i)
\*                           \/ /\ ~IsQuorum(newLearners) \* leader switches to looking
\*                              /\ LeaderShutdown(leader)
\*                              /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
\*                     \/ /\ ~connectedWithLeader
\*                        /\ FollowerShutdown(i)
\*                        /\ CleanInputBuffer({i})
\*                        /\ UNCHANGED <<learners, cepochRecv, ackeRecv, ackldRecv>>
\*            \/ /\ IsLeader(i)
\*               /\ LeaderShutdown(i)
\*               /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
\*         /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> 0,
\*                                                            zxid  |-> <<0, 0>> ] ]
\*         /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, sendCounter, leaderOracle>>
\*         /\ UpdateRecorder(<<"Restart", i>>)
-----------------------------------------------------------------------------

(* Establish connection between leader and follower. *)
ConnectAndFollowerSendCEPOCH(i, j) ==
    /\ IsLeader(i) 
    /\ ~IsMyLearner(i, j)
    /\ IsFollower(j) 
    /\ HasNoLeader(j) 
    /\ leaderOracle = i
    /\ learners'   = [learners   EXCEPT ![i] = learners[i] \cup {j}]
    /\ connectInfo' = [connectInfo EXCEPT ![j] = i]
    /\ mesgs' = mesgs \* Send(j, i, [ mtype  |-> CEPOCH, mepoch |-> acceptedEpoch[j] ]) \* contains f.p
    /\ CEPOCHmsgs' = CEPOCHmsgs \cup {[ mtype  |-> CEPOCH, mepoch |-> acceptedEpoch[j], msrc |-> j, mdst |-> i, morder |-> 0 ]}
    /\ UNCHANGED <<serverVars, electionVars, cepochRecv, ackeRecv, ackldRecv, sendCounter, NEWEPOCHmsgs, ACKEPOCHmsgs, NEWLEADERmsgs, ACKLDmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

CepochRecvQuorumFormed(i) == LET sid_cepochRecv == {c.sid: c \in cepochRecv[i]} IN IsQuorum(sid_cepochRecv)
CepochRecvBecomeQuorum(i) == LET sid_cepochRecv == {c.sid: c \in cepochRecv'[i]} IN IsQuorum(sid_cepochRecv)

\* @type: (Set({ sid: SERVER, connected: Bool, epoch: Int }), SERVER, Int) => Set({ sid: SERVER, connected: Bool, epoch: Int });
UpdateCepochRecv(oldSet, sid, peerEpoch) ==
        IF sid \in {s.sid: s \in oldSet}
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                    new_info == [ sid       |-> sid,
                                  connected |-> TRUE,
                                  epoch     |-> peerEpoch ]
                IN ( oldSet \ {old_info} ) \union {new_info}
           ELSE LET follower_info == [ sid       |-> sid,
                                       connected |-> TRUE,
                                       epoch     |-> peerEpoch ]
                IN oldSet \union {follower_info}

\* Determine new e' in this round from a quorum of CEPOCH.
DetermineNewEpoch(i) ==
        LET epoch_cepochRecv == {c.epoch: c \in cepochRecv'[i]}
        IN Maximum(epoch_cepochRecv) + 1

(* Leader waits for receiving FOLLOWERINFO from a quorum including itself,
   and chooses a new epoch e' as its own epoch and broadcasts NEWEPOCH. *)
LeaderProcessCEPOCH(i, j, cepochMsg) ==
        \* /\ CheckEpoch  \* test restrictions of max epoch
    \* \E cepochMsg \in CEPOCHmsgs
        /\ IsLeader(i)
        \* /\ PendingCEPOCH(i, j)
        /\ cepochMsg.mdst = i
        /\ cepochMsg.msrc = j
        \* /\ cepochMsg.morder = MinMsgOrder(j,i)
        /\ LET msg == mesgs[j][i][1]
               infoOk == IsMyLearner(i, j)
           IN /\ infoOk
              /\ \/ \* 1. has not broadcast NEWEPOCH
                    /\ ~CepochRecvQuorumFormed(i)
                    /\ zabState[i] = DISCOVERY
                    \* /\ UNCHANGED violatedInvariants
                    /\ cepochRecv' = [cepochRecv EXCEPT ![i] = UpdateCepochRecv(cepochRecv[i], j, cepochMsg.mepoch) ]
                    /\ \/ \* 1.1. cepochRecv becomes quorum, 
                          \* then determine e' and broadcasts NEWEPOCH in Q. 
                          /\ CepochRecvBecomeQuorum(i)
                          /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = DetermineNewEpoch(i)]
                          /\ CEPOCHmsgs' = CEPOCHmsgs \ {cepochMsg}
                          /\ LET m == [ mtype  |-> NEWEPOCH,
                                        mepoch |-> acceptedEpoch'[i] ]
                             IN DiscardAndBroadcastNEWEPOCH(i, j, m)
                       \/ \* 1.2. cepochRecv still not quorum.
                          /\ ~CepochRecvBecomeQuorum(i)
                          /\ mesgs' = mesgs \* DiscardIn(msgs ,j, i)
                          /\ CEPOCHmsgs' = CEPOCHmsgs \ {cepochMsg}
                          /\ UNCHANGED <<acceptedEpoch, NEWEPOCHmsgs>>
                 \/ \* 2. has broadcast NEWEPOCH
                    /\ CepochRecvQuorumFormed(i)
                    /\ cepochRecv' = [cepochRecv EXCEPT ![i] = UpdateCepochRecv(cepochRecv[i], j, cepochMsg.mepoch) ]
                    /\ mesgs' = mesgs
                    /\ CEPOCHmsgs' = CEPOCHmsgs \ {cepochMsg}
                    /\ NEWEPOCHmsgs' = NEWEPOCHmsgs \cup 
                                        {[ mtype  |-> NEWEPOCH,
                                           mepoch |-> acceptedEpoch[i], msrc |-> i, mdst |-> j, morder |-> 0 ]}
                    /\ UNCHANGED <<acceptedEpoch>>
        /\ UNCHANGED <<state, zabState, currentEpoch, history, lastCommitted, learners, 
                       ackeRecv, ackldRecv, sendCounter, followerVars,
                       electionVars, ACKEPOCHmsgs, NEWLEADERmsgs, ACKLDmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

(* Follower receives LEADERINFO. If newEpoch >= acceptedEpoch, then follower 
   updates acceptedEpoch and sends ACKEPOCH back, containing currentEpoch and
   history. After this, zabState turns to SYNC. *)
\* @type: (SERVER, SERVER, { mtype: Str, mepoch: Int, msrc: SERVER, mdst: SERVER, morder: Int }) => Bool;
FollowerProcessNEWEPOCH(i, j, newEpochMsg) ==
        /\ newEpochMsg \in NEWEPOCHmsgs
        /\ IsFollower(i)
        \* /\ PendingNEWEPOCH(i, j)
        /\ newEpochMsg.mdst = i
        /\ newEpochMsg.msrc = j
        \* /\ newEpochMsg.morder = MinMsgOrder(j,i)
        /\ LET \*msg     == msgs[j][i][1]
               infoOk  == IsMyLeader(i, j)
               stateOk == zabState[i] = DISCOVERY
               epochOk == newEpochMsg.mepoch >= acceptedEpoch[i]
           IN /\ infoOk
              /\ \/ \* 1. Normal case
                    /\ epochOk
                    /\ \/ /\ stateOk
                          /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = newEpochMsg.mepoch]
                          /\ LET m == [ mtype    |-> ACKEPOCH,
                                        mepoch   |-> currentEpoch[i],
                                        mhistory |-> history[i],
                                        msrc |-> i,
                                        mdst |-> j,
                                        morder |-> 0 ]
                             IN 
                            \*  /\ Reply(i, j, m)
                             /\ ACKEPOCHmsgs' = ACKEPOCHmsgs \cup {m}
                             /\ NEWEPOCHmsgs' = NEWEPOCHmsgs \ {newEpochMsg}
                          /\ zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]
                        \*   /\ UNCHANGED violatedInvariants
                    /\ UNCHANGED <<mesgs, followerVars, learners, cepochRecv, ackeRecv, ackldRecv, state, CEPOCHmsgs, NEWLEADERmsgs, ACKLDmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>
                \*
                \* Why does follower necessarily need to revert to election in this case?
                \*
                \*  \/ \* 2. Abnormal case - go back to election
                \*     /\ ~epochOk
                \*     /\ state'    = [state      EXCEPT ![i] = LOOKING]
                \*     /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
                \*     /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]
                \*     /\ LET leader == connectInfo[i]
                \*        IN \*/\ Clean(i, leader)
                \*           /\ COMMITmsgs' = {m \in COMMITmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ CEPOCHmsgs' = {m \in CEPOCHmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ NEWEPOCHmsgs' = {m \in NEWEPOCHmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ ACKEPOCHmsgs' = {m \in ACKEPOCHmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ NEWLEADERmsgs' = {m \in NEWLEADERmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ ACKLDmsgs' = {m \in ACKLDmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ COMMITLDmsgs' = {m \in COMMITLDmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ PROPOSEmsgs' = {m \in PROPOSEmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ ACKmsgs' = {m \in ACKmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           /\ COMMITmsgs' = {m \in COMMITmsgs : ~((m.msrc = i /\ m.mdst = leader) \/ (m.msrc = leader /\ m.mdst = i))}
                \*           \* /\ RemoveLearner(leader, i)
                \*           /\ learners'   = [learners   EXCEPT ![leader] = learners[leader] \ {i}] 
                \*           /\ cepochRecv' = [cepochRecv EXCEPT ![leader] = RemoveCepochRecv(cepochRecv[leader], i) ]
                \*           /\ ackeRecv'   = [ackeRecv   EXCEPT ![leader] = RemoveAckeRecv(ackeRecv[leader], i) ]
                \*           /\ ackldRecv'  = [ackldRecv  EXCEPT ![leader] = RemoveAckldRecv(ackldRecv[leader], i) ]
                \*     /\ UNCHANGED <<mesgs, acceptedEpoch>>
        /\ UNCHANGED <<currentEpoch, history, lastCommitted, sendCounter, electionVars>>

AckeRecvQuorumFormed(i) == LET sid_ackeRecv == {a.sid: a \in ackeRecv[i]} IN IsQuorum(sid_ackeRecv)
AckeRecvBecomeQuorum(i) == LET sid_ackeRecv == {a.sid: a \in ackeRecv'[i]} IN IsQuorum(sid_ackeRecv)

\* @type: (Set({ sid: SERVER, connected: Bool, peerLastEpoch: Int, peerHistory: Seq(TXN) }), SERVER, Int, Seq(TXN)) => Set({ sid: SERVER, connected: Bool, peerLastEpoch: Int, peerHistory: Seq(TXN) });
UpdateAckeRecv(oldSet, sid, peerEpoch, peerHistory) ==
        LET sid_set == {s.sid: s \in oldSet}
            follower_info == [ sid           |-> sid,
                               connected     |-> TRUE,
                               peerLastEpoch |-> peerEpoch,
                               peerHistory   |-> peerHistory ]
        IN IF sid \in sid_set 
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                IN (oldSet \ {old_info}) \union {follower_info}
           ELSE oldSet \union {follower_info}

\* for checking invariants
\* RECURSIVE SetPacketsForChecking(_,_,_,_,_,_)
\* SetPacketsForChecking(set, src, ep, his, cur, end) ==
\*         IF cur > end THEN set
\*         ELSE LET m_proposal == [ source |-> src,
\*                                  epoch  |-> ep,
\*                                  zxid   |-> his[cur].zxid,
\*                                  data   |-> his[cur].value ]
\*              IN SetPacketsForChecking((set \union {m_proposal}), src, ep, his, cur + 1, end)
    

\* TRUE: f1.a > f2.a or (f1.a = fa.a and f1.zxid >= f2.zxid)
\* @type: ({sid:SERVER, currentEpoch:Int, lastZxid:ZXID}, {sid:SERVER, currentEpoch:Int, lastZxid:ZXID}) => Bool;
MoreRecentOrEqual(ss1, ss2) == \/ ss1.currentEpoch > ss2.currentEpoch
                               \/ /\ ss1.currentEpoch = ss2.currentEpoch
                                  /\ ~ZxidCompare(ss2.lastZxid, ss1.lastZxid)

MoreRecentOrEqualFold(ss1, ss2) ==  IF MoreRecentOrEqual(ss1, ss2) THEN ss1 ELSE ss2

\* @type: (SERVER -> Set(ACKERECVTYPE), SERVER) => Seq(TXN);
DetermineInitialHistoryFromArg(ackeRecvArg, i) ==
        LET set == ackeRecvArg[i]
            ss_set == { [ sid          |-> a.sid,
                          currentEpoch |-> a.peerLastEpoch,
                          lastZxid     |-> LastZxidOfHistory(a.peerHistory) ] : a \in ackeRecvArg[i] }
            \* Choose server with most recent history.
            ss_local == [sid |-> i, currentEpoch |-> currentEpoch[i], lastZxid |-> LastZxidOfHistory(history[i])]
            selected == ApaFoldSet(MoreRecentOrEqualFold, ss_local , ss_set)
            \* CHOOSE based variant that is inefficient for Apalache.
            \* selected == CHOOSE ss \in ss_set: \A ss1 \in (ss_set \ {ss}): MoreRecentOrEqual(ss, ss1)
            info == CHOOSE f \in ackeRecvArg[i] : f.sid = selected.sid
        IN info.peerHistory

\* Determine initial history Ie' in this round from a quorum of ACKEPOCH.
\* @type: (SERVER) => Seq(TXN);
DetermineInitialHistory(i) ==
        LET set == ackeRecv'[i]
            ss_set == { [ sid          |-> a.sid,
                          currentEpoch |-> a.peerLastEpoch,
                          lastZxid     |-> LastZxidOfHistory(a.peerHistory) ]
                        : a \in set }
            ss_local == [sid |-> i, currentEpoch |-> currentEpoch[i], lastZxid |-> LastZxidOfHistory(history[i])]
            selected == ApaFoldSet(MoreRecentOrEqualFold, ss_local , ss_set)
            \* CHOOSE based variant that is inefficient for Apalache.
            \* selected == CHOOSE ss \in ss_set: \A ss1 \in (ss_set \ {ss}): MoreRecentOrEqual(ss, ss1)
            info == CHOOSE f \in set: f.sid = selected.sid
        IN info.peerHistory

\* RECURSIVE InitAcksidHelper(_,_)
\* InitAcksidHelper(txns, src) == IF Len(txns) = 0 THEN << >>
\*                                ELSE LET oldTxn == txns[1]
\*                                         newTxn == [ zxid   |-> oldTxn.zxid,
\*                                                     value  |-> oldTxn.value,
\*                                                     ackSid |-> {src},
\*                                                     epoch  |-> oldTxn.epoch ]
\*                                     IN <<newTxn>> \o InitAcksidHelper( Tail(txns), src)

\* \* Atomically let all txns in initial history contain self's acks.
\* InitAcksid(i, his) == InitAcksidHelper(his, i)

\* Atomically let all txns in initial history contain self's acks. (declarative version)
\* @type: (SERVER, Seq(TXN)) => Seq(TXN);
InitAcksid(i, his) == FunAsSeq([ind \in DOMAIN his |-> [his[ind] EXCEPT !.ackSid = {i}]], Cardinality(DOMAIN his), MaxHistLen)

\* ASSUME PrintT(InitAcksid(12, <<[zxid |-> <<2, 1>>, value |-> 0, ackSid |-> {"s3"}, epoch |-> 2]>>))

\* Eq1 == \A i \in Server : \A j \in Server : InitAcksidAlt(i,history[j]) = InitAcksid(i,history[j])

(* Leader waits for receiving ACKEPOPCH from a quorum, and determines initialHistory
   according to history of whom has most recent state summary from them. After this,
   leader's zabState turns to SYNCHRONIZATION. *)
\* Has broadcast NEWLEADER.
\* LeaderProcessACKEPOCHHasBroadcast(i, j) ==
\*         /\ IsLeader(i)
\*         /\ PendingACKEPOCH(i, j)
\*         /\ IsMyLearner(i, j)
\*         /\ LET msg == msgs[j][i][1]
\*            IN \* 1. has broadcast NEWLEADER 
\*               /\ IsQuorum({a.sid: a \in ackeRecv[i]})
\*               /\ ackeRecv' = [ackeRecv EXCEPT ![i] = UpdateAckeRecv(ackeRecv[i], j,msg.mepoch, msg.mhistory) ]
\*               /\ LET toSend == history[i] \* contains (Ie', Be')
\*                      m == [ mtype    |-> NEWLEADER,
\*                             mepoch   |-> acceptedEpoch[i],
\*                             mhistory |-> toSend ] IN 
\*                             msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m)]
\*                     \* Ignore 'proposalMsgs' updates for now and safety properties that depend on it.
\*                     \*  set_forChecking == SetPacketsForChecking({ }, i, acceptedEpoch[i], toSend, 1, Len(toSend)) IN 
\*                     \*  /\ Reply(i, j, m) 
\*                     \*  /\ proposalMsgsLog' = proposalMsgsLog \*\union set_forChecking
\*               /\ UNCHANGED <<currentEpoch, history, zabState, state, acceptedEpoch, lastCommitted, learners, cepochRecv, ackldRecv, sendCounter, followerVars, electionVars>>

(* Leader waits for receiving ACKEPOPCH from a quorum, and determines initialHistory
   according to history of whom has most recent state summary from them. After this,
   leader's zabState turns to SYNCHRONIZATION. *)
\* Has not broadcast NEWLEADER yet.
LeaderProcessACKEPOCHHasntBroadcast(i, j, ackEpochMsg) ==
    /\ IsLeader(i)
    \* /\ PendingACKEPOCH(i, j)
    /\ ackEpochMsg.mdst = i
    /\ ackEpochMsg.msrc = j
    \* /\ ackEpochMsg.morder = MinMsgOrder(j,i)
    /\ LET msg == mesgs[j][i][1]
            infoOk == IsMyLearner(i, j)
        IN  /\ infoOk
            \* 2. has not broadcast NEWLEADER
            /\ ~AckeRecvQuorumFormed(i)
            /\ zabState[i] = DISCOVERY
            /\ ackeRecv' = [ackeRecv EXCEPT ![i] = UpdateAckeRecv(@, j,ackEpochMsg.mepoch, ackEpochMsg.mhistory) ]
                \* 2.1. ackeRecv becomes quorum, determine Ie'
                \* and broacasts NEWLEADER in Q. (l.1.2 + l.2.1)
            /\  \/ /\ AckeRecvBecomeQuorum(i)
                   /\ \* Update f.a
                      LET newLeaderEpoch == acceptedEpoch[i] IN 
                      /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newLeaderEpoch]
                      /\ \* Determine initial history Ie'
                            LET initialHistory == DetermineInitialHistory(i) 
                            IN 
                            history' = [history EXCEPT ![i] = InitAcksid(i, initialHistory) ]
                      /\ zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]
                      /\ ACKEPOCHmsgs' = ACKEPOCHmsgs \ {ackEpochMsg}
                      /\ \* Broadcast NEWLEADER with (e', Ie')
                            LET toSend == history'[i] 
                                m == [  mtype    |-> NEWLEADER,
                                        mepoch   |-> acceptedEpoch[i],
                                        mhistory |-> toSend] IN DiscardAndBroadcastNEWLEADER(i, j, m, toSend)
                \/  \* 2.2. ackeRecv still not quorum.
                    /\ ~AckeRecvBecomeQuorum(i)
                    /\ mesgs' = mesgs \* Discard(j, i)
                    /\ ACKEPOCHmsgs' = ACKEPOCHmsgs \ {ackEpochMsg}
                    /\ UNCHANGED <<currentEpoch, history, zabState, NEWLEADERmsgs>>
    /\ UNCHANGED <<state, acceptedEpoch, lastCommitted, learners, cepochRecv, ackldRecv, sendCounter, followerVars, electionVars, CEPOCHmsgs, NEWEPOCHmsgs, ACKLDmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

-----------------------------------------------------------------------------    
(* Follower receives NEWLEADER. Update f.a and history. *)
FollowerProcessNEWLEADER(i, j, newLeaderMsg) ==
        /\ newLeaderMsg \in NEWLEADERmsgs
        /\ IsFollower(i)
        \* /\ PendingNEWLEADER(i, j)
        /\ newLeaderMsg.mdst = i
        /\ newLeaderMsg.msrc = j
        \* /\ newLeaderMsg.morder = MinMsgOrder(j,i)
        /\ LET msg == mesgs[j][i][1] IN
              \* 2. f.p equals e'.
              /\ IsMyLeader(i, j)
              /\ acceptedEpoch[i] = newLeaderMsg.mepoch
              /\ zabState[i] = SYNCHRONIZATION
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i]]
              /\ history' = [history EXCEPT ![i] = newLeaderMsg.mhistory] \* no need to care ackSid
              /\ LET m == [ mtype |-> ACKLD, mzxid |-> LastZxidOfHistory(history'[i]) ] IN
                        /\ mesgs' = mesgs \* [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m)]
                        /\ NEWLEADERmsgs' = NEWLEADERmsgs \ {newLeaderMsg}
                        /\ ACKLDmsgs' = ACKLDmsgs \cup {[ mtype |-> ACKLD, 
                                                          mzxid |-> LastZxidOfHistory(history'[i]), 
                                                          msrc |-> i, mdst |-> j, morder |-> 0 ]}
              /\ UNCHANGED <<followerVars, state, zabState, learners, cepochRecv, ackeRecv, ackldRecv, acceptedEpoch, lastCommitted, sendCounter, electionVars, CEPOCHmsgs, NEWEPOCHmsgs, ACKEPOCHmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

\* FollowerProcessNEWLEADERNewIteration(i, j) ==
\*         /\ IsFollower(i)
\*         /\ PendingNEWLEADER(i, j)
\*         /\ LET msg == msgs[j][i][1]
\*                infoOk == IsMyLeader(i, j)
\*                epochOk == acceptedEpoch[i] = msg.mepoch
\*                stateOk == zabState[i] = SYNCHRONIZATION
\*            IN /\ infoOk
\*               \* 1. f.p not equals e', starts a new iteration.
\*               /\ ~epochOk
\*               /\ state'    = [state      EXCEPT ![i] = LOOKING]
\*               /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
\*               /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]
\*               /\ LET leader == connectInfo[i]
\*                   IN /\ Clean(i, leader)
\*                      /\ RemoveLearner(leader, i)
\*               /\ UNCHANGED <<currentEpoch, history, acceptedEpoch, lastCommitted, sendCounter, electionVars>>

AckldRecvQuorumFormed(i) == LET sid_ackldRecv == {a.sid: a \in ackldRecv[i]} IN IsQuorum(sid_ackldRecv)
AckldRecvBecomeQuorum(i) == LET sid_ackldRecv == {a.sid: a \in ackldRecv'[i]} IN IsQuorum(sid_ackldRecv)

\* @type: (Set({ sid: SERVER, connected: Bool }), SERVER) => Set({ sid: SERVER, connected: Bool });
UpdateAckldRecv(oldSet, sid) ==
        LET sid_set == {s.sid: s \in oldSet}
            follower_info == [ sid       |-> sid,
                               connected |-> TRUE ]
        IN IF sid \in sid_set
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                IN (oldSet \ {old_info}) \union {follower_info}
           ELSE oldSet \union {follower_info}


\* RECURSIVE UpdateAcksidHelper(_,_,_)
\* UpdateAcksidHelper(txns, target, endZxid) ==
\*         IF Len(txns) = 0 THEN << >>
\*         ELSE LET oldTxn == txns[1]
\*              IN IF ZxidCompare(oldTxn.zxid, endZxid) THEN txns
\*                 ELSE LET newTxn == [ zxid   |-> oldTxn.zxid,
\*                                      value  |-> oldTxn.value,
\*                                      ackSid |-> IF target \in oldTxn.ackSid
\*                                                 THEN oldTxn.ackSid
\*                                                 ELSE oldTxn.ackSid \union {target},
\*                                      epoch  |-> oldTxn.epoch ]
\*                      IN <<newTxn>> \o UpdateAcksidHelper( Tail(txns), target, endZxid)
    
\* @type: (Seq(TXN), SERVER, ZXID) => Seq(TXN);
UpdateAcksidIter(his, target, endZxid) == 
    LET zxidIndicesLessThanEnd == {i \in DOMAIN his : ~ZxidCompare(his[i].zxid, endZxid)}
        firstZxidIndex == IF zxidIndicesLessThanEnd # {} 
                            THEN Maximum(zxidIndicesLessThanEnd)
                            ELSE 100 IN
    FunAsSeq([idx \in DOMAIN his |-> 
        IF firstZxidIndex >= 0 /\ idx <= firstZxidIndex 
            THEN [his[idx] EXCEPT !.ackSid = his[idx].ackSid \cup {target}]
            ELSE his[idx]
    ], Cardinality(DOMAIN his), MaxHistLen)

\* Atomically add ackSid of one learner according to zxid in ACKLD.
UpdateAcksid(his, target, endZxid) == UpdateAcksidIter(his, target, endZxid)

\* TODO: Get this working properly.
\* UpdateAcksAreEquiv == 
    \* \A s,t \in Server : \A zxid \in (1..MaxEpoch) \X (1..MaxEpoch) : 
    \* /\ PrintT(zxid)
    \* /\ PrintT(t)
    \* /\ PrintT(UpdateAcksid(history[s], t, zxid))
    \* /\ PrintT(UpdateAcksidExpr(history[s], t, zxid))
    \* /\ UpdateAcksidHelper(history[s], t, zxid) = UpdateAcksidIter(history[s], t, zxid) 

(* Leader waits for receiving ACKLD from a quorum including itself,
   and broadcasts COMMITLD and turns to BROADCAST. *)
LeaderProcessACKLDHasntBroadcast(i, j, ackldMsg) ==
        /\ IsLeader(i)
        \* /\ PendingACKLD(i, j)
        /\ ackldMsg.mdst = i
        /\ ackldMsg.msrc = j
        \* /\ ackldMsg.morder = MinMsgOrder(j,i)
        /\ LET msg == mesgs[j][i][1] IN
              /\ IsMyLearner(i, j)
              \* 1. has not broadcast COMMITLD
              /\ ~AckldRecvQuorumFormed(i)
              /\ zabState[i] = SYNCHRONIZATION 
              /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(ackldRecv[i], j) ]
              /\ history' = [history EXCEPT ![i] = UpdateAcksid(history[i], j, ackldMsg.mzxid)]
                    \* 1.1. ackldRecv becomes quorum,
                    \* then broadcasts COMMITLD and turns to BROADCAST.
              /\ \/ /\ AckldRecvBecomeQuorum(i)
                    /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> Len(history[i]), zxid  |-> LastZxid(i) ] ]
                    /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
                    /\ ACKLDmsgs' = ACKLDmsgs \ {ackldMsg}
                    /\ LET m == [ mtype |-> COMMITLD, mzxid |-> LastZxid(i) ] IN DiscardAndBroadcastCOMMITLD(i, j, m)
                 \/ \* 1.2. ackldRecv still not quorum.
                    /\ ~AckldRecvBecomeQuorum(i)
                    /\ mesgs' = mesgs \* Discard(j, i)
                    /\ ACKLDmsgs' = ACKLDmsgs \ {ackldMsg}
                    /\ UNCHANGED <<zabState, lastCommitted, COMMITLDmsgs>>
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, sendCounter, followerVars, electionVars, CEPOCHmsgs, NEWEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

\* LeaderProcessACKLDHasBroadcastNoQuorum(i, j) ==
\*         /\ IsLeader(i)
\*         /\ PendingACKLD(i, j)
\*         /\ LET msg == msgs[j][i][1]
\*                infoOk == IsMyLearner(i, j)
\*            IN /\ infoOk
\*               /\ \/ \* 1. has not broadcast COMMITLD
\*                     /\ ~AckldRecvQuorumFormed(i)
\*                     /\ \/ /\ zabState[i] = SYNCHRONIZATION
\*                     /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(@, j) ]
\*                     /\ history' = [history EXCEPT ![i] = UpdateAcksid(@, j, msg.mzxid)]
\*                     \* 1.2. ackldRecv still not quorum.
\*                     /\ ~AckldRecvBecomeQuorum(i)
\*                     /\ Discard(j, i)
\*                     /\ UNCHANGED <<zabState, lastCommitted>>
\*         /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, sendCounter, followerVars, electionVars>>


(* Leader waits for receiving ACKLD from a quorum including itself,
   and broadcasts COMMITLD and turns to BROADCAST. *)
\* LeaderProcessACKLDHasBroadcast(i, j) ==
\*         /\ IsLeader(i)
\*         /\ PendingACKLD(i, j)
\*         /\ AckldRecvQuorumFormed(i)
\*         /\ IsMyLearner(i, j)
\*         /\ LET msg == msgs[j][i][1] IN
\*               \* 2. has broadcast COMMITLD
\*               /\ zabState[i] = BROADCAST 
\*               /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(@, j) ]
\*               /\ history' = [history EXCEPT ![i] = UpdateAcksid(@, j, msg.mzxid)]
\*             \*   /\ history' = [history EXCEPT ![i] = UpdateAcksidExpr(@, j, msg.mzxid)] \* TODO: Eventually switch to this.
\*               /\ msgs' = [msgs EXCEPT 
\*                             ![j][i] = Tail(msgs[j][i]), 
\*                             ![i][j] = Append(msgs[i][j], [ mtype |-> COMMITLD, mzxid |-> lastCommitted[i].zxid ])]
\*         /\ UNCHANGED <<zabState, lastCommitted, state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, sendCounter, followerVars, electionVars, CEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs, NEWEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>

\* RECURSIVE ZxidToIndexHepler(_,_,_,_)
\* ZxidToIndexHepler(his, zxid, cur, appeared) == 
\*         IF cur > Len(his) THEN cur  
\*         ELSE IF TxnZxidEqual(his[cur], zxid) 
\*              THEN (IF appeared = TRUE 
\*                     THEN -1 
\*                     ELSE Minimum( { cur, ZxidToIndexHepler(his, zxid, cur + 1, TRUE) } ))
\*              ELSE ZxidToIndexHepler(his, zxid, cur + 1, appeared)

\* \* return -1: this zxid appears at least twice. 
\* \* Len(his) + 1: does not exist.
\* \* 1 - Len(his): exists and appears just once.
\* ZxidToIndexRec(his, zxid) == 
\*     IF ZxidEqual( zxid, <<0, 0>> ) THEN 0
\*         ELSE 
\*             IF Len(his) = 0 THEN 1
\*             ELSE LET len == Len(his) IN
\*                 IF \E idx \in 1..len: TxnZxidEqual(his[idx], zxid)
\*                     THEN ZxidToIndexHepler(his, zxid, 1, FALSE)
\*                     ELSE len + 1

\* Non-recursive version.
ZxidToIndexIter(his, zxid) == 
    IF ZxidEqual(zxid, <<0, 0>>) THEN 0
        ELSE IF Len(his) = 0 THEN 1

        ELSE LET inds == {ind \in DOMAIN his : TxnZxidEqual(his[ind], zxid)} IN
                IF Cardinality(inds) = 1 \* zxid appears exactly once.
                THEN CHOOSE v \in inds : TRUE
            ELSE 
                IF Cardinality(inds) >= 2 THEN -1 \* zxid appears at least twice.
                ELSE Len(his) + 1

ZxidToIndex(his, zxid) == ZxidToIndexIter(his, zxid)

\* Checking equivalence of iterative and recursive versions of this operator.
\* ZxidToIndexEquiv == 
    \* \A s \in Server :
    \* \A x,y,z \in {1,2,3} : 
        \* /\ PrintT("history:")
        \* /\ PrintT(history[s])
        \* /\ PrintT(<<x,y>>)
        \* /\ PrintT(ZxidToIndexExpr(history[s], <<x,y>>))
        \* /\ PrintT(ZxidToIndex(history[s], <<x,y>>))
        \* /\ PrintT("custom val:")
        \* /\ PrintT(ZxidToIndex(<<[zxid |-> <<1, 1>>, value |-> 0], [zxid |-> <<2, 1>>, value |-> 0]>>, <<1,1>>))
        \* /\ ZxidToIndexIter(history[s], <<x,y>>) = ZxidToIndexRec(history[s], <<x,y>>)

(* Follower receives COMMITLD. Commit all txns. *)
\* @type: (SERVER, SERVER, { mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER, morder: Int }) => Bool;
FollowerProcessCOMMITLD(i, j, commitLDmsg) ==
        /\ commitLDmsg \in COMMITLDmsgs
        /\ IsFollower(i)
        \* /\ PendingCOMMITLD(i, j)
        /\ commitLDmsg.mdst = i
        /\ commitLDmsg.msrc = j
        \* /\ commitLDmsg.morder = MinMsgOrder(j,i)
        /\ IsMyLeader(i, j)
        /\ LET msg == mesgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               index == IF ZxidEqual(commitLDmsg.mzxid, <<0, 0>>) 
                            THEN 0
                            ELSE ZxidToIndex(history[i], commitLDmsg.mzxid)
               logOk == index >= 0 /\ index <= Len(history[i])
           IN /\ infoOk
              /\ logOk
              /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> index,
                                                                 zxid  |-> commitLDmsg.mzxid ] ]
              /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
              \* Discard the message. (Will S. 10/26/23)
              /\ mesgs' = mesgs \* [msgs EXCEPT ![j][i] = Tail(msgs[j][i])]
              /\ COMMITLDmsgs' = COMMITLDmsgs \ {commitLDmsg}
              /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, history, leaderVars, followerVars, electionVars, CEPOCHmsgs, ACKLDmsgs, NEWEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs, PROPOSEmsgs, ACKmsgs, COMMITmsgs>>
----------------------------------------------------------------------------
\* @type: (SERVER, ZXID) => ZXID;
IncZxid(s, zxid) == IF currentEpoch[s] = zxid[1] THEN <<zxid[1], zxid[2] + 1>>
                    ELSE <<currentEpoch[s], 1>>

(* Leader receives client request.
   Note: In production, any server in traffic can receive requests and 
         forward it to leader if necessary. We choose to let leader be
         the sole one who can receive write requests, to simplify spec 
         and keep correctness at the same time. *)
LeaderProcessRequest(i) ==
        \* /\ CheckTransactionNum \* test restrictions of transaction num
        \E val \in {0,1} :  \* pick some val.
            /\ IsLeader(i)
            /\ zabState[i] = BROADCAST
            /\ LET request_value == val
                \* GetRecorder("nClientRequest") \* unique value
                newTxn == [ zxid   |-> IncZxid(i, LastZxid(i)),
                            value  |-> request_value,
                            ackSid |-> {i},
                            epoch  |-> currentEpoch[i] ]
                IN history' = [history EXCEPT ![i] = Append(@, newTxn) ]
            /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, lastCommitted, leaderVars, followerVars, electionVars, msgVars>>

\* Latest counter existing in history.
CurrentCounter(i) == IF LastZxid(i)[1] = currentEpoch[i] THEN LastZxid(i)[2]
                     ELSE 0

(* Leader broadcasts PROPOSE when sendCounter < currentCounter. *)
\* @type: SERVER => Bool;
LeaderBroadcastPROPOSE(i) == 
        /\ IsLeader(i)
        /\ zabState[i] = BROADCAST
        /\ sendCounter[i] < CurrentCounter(i) \* there exists proposal to be sent
         \* Explicit check here to avoid out-of-bounds access. (Will S. 10/26/23)
        /\ ZxidToIndex(history[i], <<currentEpoch[i], sendCounter[i] + 1>>) \in DOMAIN history[i]
        /\ LET toSendCounter == sendCounter[i] + 1
               toSendIndex == ZxidToIndex(history[i], <<currentEpoch[i], toSendCounter>>)
               toSendTxn == history[i][toSendIndex]
               m_proposal == [ mtype |-> PROPOSE,
                               mzxid |-> toSendTxn.zxid,
                               mdata |-> toSendTxn.value ]
           IN /\ sendCounter' = [sendCounter EXCEPT ![i] = toSendCounter]
              /\ mesgs' = mesgs \* Broadcast(i, m_proposal)
              /\ LET ackeRecv_quorum == {a \in ackeRecv[i]: a.connected = TRUE }
                     sid_ackeRecv == { a.sid: a \in ackeRecv_quorum } IN
                        PROPOSEmsgs' = PROPOSEmsgs \cup {
                                        [ mtype |-> PROPOSE,
                                          mzxid |-> toSendTxn.zxid,
                                          mdata |-> toSendTxn.value,
                                          msrc |-> i,
                                          mdst |-> to ] : to \in (sid_ackeRecv \cap learners[i]) \ {i}}
        /\ UNCHANGED <<serverVars, learners, cepochRecv, ackeRecv, ackldRecv, followerVars, electionVars, CEPOCHmsgs, COMMITLDmsgs, ACKLDmsgs, NEWEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs, ACKmsgs, COMMITmsgs>>

\* @type: (ZXID, ZXID) => Bool;
IsNextZxid(curZxid, nextZxid) ==
            \/ \* first PROPOSAL in this epoch
               /\ nextZxid[2] = 1
               /\ curZxid[1] < nextZxid[1]
            \/ \* not first PROPOSAL in this epoch
               /\ nextZxid[2] > 1
               /\ curZxid[1] = nextZxid[1]
               /\ curZxid[2] + 1 = nextZxid[2]

(* Follower processes PROPOSE, saves it in history and replies ACK. *)
\* @type: (SERVER, SERVER, { mtype: Str, mzxid: ZXID, mdata: Int, msrc: SERVER, mdst: SERVER }) => Bool;
FollowerProcessPROPOSE(i, j, proposeMsg) ==
        /\ proposeMsg \in PROPOSEmsgs
        /\ IsFollower(i)
        \* /\ PendingPROPOSE(i, j)
        /\ proposeMsg.mdst = i
        /\ proposeMsg.msrc = j
        /\ LET \*msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               isNext == IsNextZxid(LastZxid(i), proposeMsg.mzxid)
               newTxn == [ zxid   |-> proposeMsg.mzxid,
                           value  |-> proposeMsg.mdata,
                           ackSid |-> {},
                           epoch  |-> currentEpoch[i] ]
               m_ack == [ mtype |-> ACK,
                          mzxid |-> proposeMsg.mzxid,
                          msrc |-> i, 
                          mdst |-> j] IN
              /\ infoOk
              /\ \/ /\ isNext
                    /\ history' = [history EXCEPT ![i] = Append(@, newTxn)]
                    /\ mesgs' = mesgs \* [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m_ack)]
                    /\ ACKmsgs' = ACKmsgs \cup {m_ack}
                    /\ UNCHANGED PROPOSEmsgs
                 \/ /\ ~isNext
                    /\ LET index == ZxidToIndex(history[i], proposeMsg.mzxid)
                           exist == index > 0 /\ index <= Len(history[i]) IN exist
                    \* /\ Discard(j, i)
                    /\ PROPOSEmsgs' = PROPOSEmsgs \ {proposeMsg}
                    /\ UNCHANGED <<history,mesgs, ACKmsgs>>
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, lastCommitted, leaderVars, followerVars, electionVars, COMMITLDmsgs, COMMITmsgs, CEPOCHmsgs, ACKLDmsgs, NEWLEADERmsgs, NEWEPOCHmsgs, ACKEPOCHmsgs>>

\* @type: (SERVER, Int, ZXID, TXN, SERVER, { mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER }) => Bool;
LeaderTryToCommit(s, index, zxid, newTxn, follower, ackMsg) ==
           \/ /\ \* Current conditions do not satisfy committing the proposal.
                 \/ ~(lastCommitted[s].index >= index - 1)
                 \/ ~IsQuorum(newTxn.ackSid)
              /\ mesgs' = mesgs \* Discard(follower, s)
              /\ ACKmsgs' = ACKmsgs \ {ackMsg}
              /\ UNCHANGED <<lastCommitted, COMMITmsgs>>
           \/ /\ (lastCommitted[s].index >= index - 1)
              /\ IsQuorum(newTxn.ackSid)
              /\ lastCommitted[s].index + 1 = index
              /\ lastCommitted' = [lastCommitted EXCEPT ![s] = [ index |-> index,
                                                                 zxid  |-> zxid ] ]
              /\ LET m_commit == [ mtype |-> COMMIT,
                                   mzxid |-> zxid ]
                     ackldRecv_quorum == {a \in ackldRecv[s]: a.connected = TRUE }
                     sid_ackldRecv == { a.sid: a \in ackldRecv_quorum }
                 IN /\ mesgs' = mesgs \* DiscardAndBroadcast(s, follower, m_commit)
                    /\ ACKmsgs' = ACKmsgs \ {ackMsg}
                    /\ COMMITmsgs' = COMMITmsgs \cup {[ 
                                        mtype |-> COMMIT,
                                        mzxid |-> zxid, 
                                        msrc |-> s, mdst |-> to] : to \in (sid_ackldRecv \cap learners[s]) \ {s}}


LastAckIndexFromFollower(i, j) == 
        LET set_index == {idx \in DOMAIN history[i] : j \in history[i][idx].ackSid }
        IN Maximum(set_index)


(* Leader Keeps a count of acks for a particular proposal, and try to
   commit the proposal. If committed, COMMIT of proposal will be broadcast. *)
\* @type: (SERVER, SERVER, { mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER }) => Bool;
LeaderProcessACK(i, j, ackMsg) ==
        /\ ackMsg \in ACKmsgs
        /\ IsLeader(i)
        \* /\ PendingACK(i, j)
        /\ ackMsg.mdst = i
        /\ ackMsg.msrc = j
        /\ LET msg == mesgs[j][i][1]
               infoOk == IsMyLearner(i, j)
               index == ZxidToIndex(history[i], ackMsg.mzxid)
               exist == index >= 1 /\ index <= Len(history[i]) \* proposal exists in history
               outstanding == lastCommitted[i].index < Len(history[i]) \* outstanding not null
               hasCommitted == ~ZxidCompare(ackMsg.mzxid, lastCommitted[i].zxid)
               ackIndex == LastAckIndexFromFollower(i, j)
               monotonicallyInc == \/ ackIndex = -1
                                   \/ ackIndex + 1 = index
           IN /\ infoOk
              /\ exist
              /\ monotonicallyInc
              /\ LET txn == history[i][index]
                           txnAfterAddAck == [ zxid   |-> txn.zxid,
                                               value  |-> txn.value,
                                               ackSid |-> txn.ackSid \union {j} , \* record the new ack for this entry.
                                               epoch  |-> txn.epoch ]   
                       IN
                       /\ history' = [history EXCEPT ![i][index] = txnAfterAddAck ]
                       /\ /\ outstanding
                          /\ ~hasCommitted
                          /\ LeaderTryToCommit(i, index, ackMsg.mzxid, txnAfterAddAck, j, ackMsg)
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, leaderVars, followerVars, electionVars, COMMITLDmsgs, PROPOSEmsgs, CEPOCHmsgs, ACKLDmsgs, NEWEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs>>

(* Leader Keeps a count of acks for a particular proposal, and try to
   commit the proposal. If committed, COMMIT of proposal will be broadcast. *)
\* LeaderProcessACKAlreadyCommitted(i, j) ==
\*         /\ IsLeader(i)
\*         /\ PendingACK(i, j)
\*         /\ LET msg == msgs[j][i][1]
\*                infoOk == IsMyLearner(i, j)
\*                index == ZxidToIndex(history[i], msg.mzxid)
\*                exist == index >= 1 /\ index <= Len(history[i]) \* proposal exists in history
\*                outstanding == lastCommitted[i].index < Len(history[i]) \* outstanding not null
\*                hasCommitted == ~ZxidCompare(msg.mzxid, lastCommitted[i].zxid)
\*                ackIndex == LastAckIndexFromFollower(i, j)
\*                monotonicallyInc == \/ ackIndex = -1
\*                                    \/ ackIndex + 1 = index
\*            IN /\ infoOk
\*               /\ exist
\*               /\ monotonicallyInc
\*               /\ LET txn == history[i][index]
\*                      txnAfterAddAck == [ zxid   |-> txn.zxid,
\*                                                value  |-> txn.value,
\*                                                ackSid |-> txn.ackSid \union {j} ,
\*                                                epoch  |-> txn.epoch ] IN
\*                        /\ history' = [history EXCEPT ![i][index] = txnAfterAddAck ]
\*                        /\ \* Note: outstanding is 0. 
\*                             \* / proposal has already been committed.
\*                             \/ ~outstanding
\*                             \/ hasCommitted
\*                        /\ Discard(j, i)
\*                        /\ UNCHANGED <<lastCommitted>>
\*         /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, leaderVars, followerVars, electionVars>>

(* Follower processes COMMIT. *)
\* @type: (SERVER, SERVER, { mtype: Str, mzxid: ZXID, msrc: SERVER, mdst: SERVER }) => Bool;
FollowerProcessCOMMIT(i, j, commitMsg) ==
        /\ commitMsg \in COMMITmsgs
        /\ IsFollower(i)
        \* /\ PendingCOMMIT(i, j)
        /\ commitMsg.mdst = i
        /\ commitMsg.msrc = j
        /\ LET msg == mesgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               pending == lastCommitted[i].index < Len(history[i])
           IN /\ infoOk
              /\ pending
              /\ LET firstElement == history[i][lastCommitted[i].index + 1]
                     match == ZxidEqual(firstElement.zxid, commitMsg.mzxid) IN
                    /\ match
                    /\ lastCommitted' = [lastCommitted EXCEPT ![i] = 
                                            [   index |-> lastCommitted[i].index + 1,
                                                zxid  |-> firstElement.zxid ] ]
        /\ mesgs' = mesgs \* Discard(j, i)
        /\ COMMITmsgs' = COMMITmsgs \ {commitMsg}
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, history,leaderVars, followerVars, electionVars, COMMITLDmsgs, PROPOSEmsgs, ACKmsgs, CEPOCHmsgs, ACKLDmsgs, NEWEPOCHmsgs, NEWLEADERmsgs, ACKEPOCHmsgs>>


----------------------------------------------------------------------------     

(* Used to discard some messages which should not exist in network channel.
   This action should not be triggered. *)
\* FilterNonexistentMessage(i) ==
\*         /\ \E j \in Server \ {i}: /\ msgs[j][i] /= << >>
\*                                   /\ LET msg == msgs[j][i][1]
\*                                      IN 
\*                                         \/ /\ IsLeader(i)
\*                                            /\ LET infoOk == IsMyLearner(i, j)
\*                                               IN
\*                                               \/ msg.mtype = NEWEPOCH
\*                                               \/ msg.mtype = NEWLEADER
\*                                               \/ msg.mtype = COMMITLD
\*                                               \/ msg.mtype = PROPOSE
\*                                               \/ msg.mtype = COMMIT
\*                                               \/ /\ ~infoOk
\*                                                  /\ \/ msg.mtype = CEPOCH
\*                                                     \/ msg.mtype = ACKEPOCH
\*                                                     \/ msg.mtype = ACKLD
\*                                                     \/ msg.mtype = ACK
\*                                         \/ /\ IsFollower(i)
\*                                            /\ LET infoOk == IsMyLeader(i, j) 
\*                                               IN
\*                                               \/ msg.mtype = CEPOCH
\*                                               \/ msg.mtype = ACKEPOCH
\*                                               \/ msg.mtype = ACKLD
\*                                               \/ msg.mtype = ACK
\*                                               \/ /\ ~infoOk
\*                                                  /\ \/ msg.mtype = NEWEPOCH
\*                                                     \/ msg.mtype = NEWLEADER
\*                                                     \/ msg.mtype = COMMITLD
\*                                                     \/ msg.mtype = PROPOSE
\*                                                     \/ msg.mtype = COMMIT   
\*                                         \/ IsLooking(i)
\*                                   /\ Discard(j, i)
\*         \* /\ violatedInvariants' = violatedInvariants
\*         \* /\ violatedInvariants' = [violatedInvariants EXCEPT !.messageIllegal = TRUE]
\*         /\ UNCHANGED <<serverVars, leaderVars, followerVars, electionVars>>
----------------------------------------------------------------------------

(* Election *)
UpdateLeaderAction == TRUE /\ \E i \in Server:    UpdateLeader(i)
FollowLeaderMyselfAction == TRUE /\ \E i \in Server:    FollowLeaderMyself(i)
FollowLeaderOtherAction == TRUE /\ \E i \in Server:    FollowLeaderOther(i)

(* Abnormal situations like failure, network disconnection *)
\* TimeoutWithQuorumAction == TRUE /\ \E i, j \in Server : TimeoutWithQuorum(i, j)
TimeoutNoQuorumAction == TRUE /\ \E i, j \in Server : TimeoutNoQuorum(i, j)

\* RestartAction == TRUE /\ \E i \in Server:    Restart(i)

(* Zab module - Discovery part *)
ConnectAndFollowerSendCEPOCHAction == TRUE /\ \E i, j \in Server: ConnectAndFollowerSendCEPOCH(i, j)
LeaderProcessCEPOCHAction == TRUE /\ \E i, j \in Server : \E msg \in CEPOCHmsgs : LeaderProcessCEPOCH(i, j, msg)
FollowerProcessNEWEPOCHAction == TRUE /\ \E i, j \in Server: \E msg \in NEWEPOCHmsgs : FollowerProcessNEWEPOCH(i, j, msg)

(* Zab module - Synchronization *)
LeaderProcessACKEPOCHHasntBroadcastAction == TRUE /\ \E i, j \in Server: \E msg \in ACKEPOCHmsgs : LeaderProcessACKEPOCHHasntBroadcast(i, j, msg)
\* LeaderProcessACKEPOCHHasBroadcastAction == TRUE /\ \E i, j \in Server: LeaderProcessACKEPOCHHasBroadcast(i, j)
FollowerProcessNEWLEADERAction == TRUE /\ \E i, j \in Server: \E msg \in NEWLEADERmsgs : FollowerProcessNEWLEADER(i, j, msg)
\* FollowerProcessNEWLEADERNewIterationAction == TRUE /\ \E i, j \in Server: FollowerProcessNEWLEADERNewIteration(i, j)
LeaderProcessACKLDHasntBroadcastAction == TRUE /\ \E i, j \in Server: \E msg \in ACKLDmsgs : LeaderProcessACKLDHasntBroadcast(i, j, msg)
\* LeaderProcessACKLDHasBroadcastAction == TRUE /\ \E i, j \in Server: LeaderProcessACKLDHasBroadcast(i, j)
FollowerProcessCOMMITLDAction == TRUE /\ \E i, j \in Server: \E msg \in COMMITLDmsgs : FollowerProcessCOMMITLD(i, j, msg)

(* Zab module - Broadcast part *)
LeaderProcessRequestAction == TRUE /\ \E i \in Server:    LeaderProcessRequest(i)
LeaderBroadcastPROPOSEAction == TRUE /\ \E i \in Server:    LeaderBroadcastPROPOSE(i)
FollowerProcessPROPOSEAction == TRUE /\ \E i, j \in Server: \E msg \in PROPOSEmsgs : FollowerProcessPROPOSE(i, j, msg)
LeaderProcessACKAction == TRUE /\ \E i, j \in Server: \E msg \in ACKmsgs : LeaderProcessACK(i, j, msg)
\* LeaderProcessACKAlreadyCommittedAction == TRUE /\ \E i, j \in Server: LeaderProcessACKAlreadyCommitted(i, j)
FollowerProcessCOMMITAction == TRUE /\ \E i, j \in Server: \E msg \in COMMITmsgs : FollowerProcessCOMMIT(i, j, msg)

(* An action used to judge whether there are redundant messages in network *)
\* FilterNonexistentMessageAction == TRUE /\ \E i \in Server:    FilterNonexistentMessage(i)

\* Complete transition relation.
Next == 
    \/ UpdateLeaderAction
    \/ FollowLeaderMyselfAction
    \/ FollowLeaderOtherAction
    \* Disable these actions for now.
    \* \/ TimeoutWithQuorumAction
    \/ TimeoutNoQuorumAction
    \* \/ RestartAction
    \/ ConnectAndFollowerSendCEPOCHAction
    \/ LeaderProcessCEPOCHAction
    \/ FollowerProcessNEWEPOCHAction
    \/ LeaderProcessACKEPOCHHasntBroadcastAction
    \* \* \/ LeaderProcessACKEPOCHHasBroadcastAction
    \/ FollowerProcessNEWLEADERAction
    \* \* \/ FollowerProcessNEWLEADERNewIterationAction
    \/ LeaderProcessACKLDHasntBroadcastAction
    \* \* \/ LeaderProcessACKLDHasBroadcastAction
    \/ FollowerProcessCOMMITLDAction
    \/ LeaderProcessRequestAction
    \/ LeaderBroadcastPROPOSEAction
    \/ FollowerProcessPROPOSEAction
    \/ LeaderProcessACKAction
    \* \* \/ LeaderProcessACKAlreadyCommittedAction
    \/ FollowerProcessCOMMITAction
    \* \/ FilterNonexistentMessageAction

\* The complete specification.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Define safety properties of Zab.

\* Inv1 == ~(\E s \in Server : state[s] = LEADING)
DebugInv1 == ~(\E s,t \in Server : 
                    /\ s # t
                    /\ state[s] = LEADING /\ Len(history[s]) > 1 /\ lastCommitted[s].index > 0 /\ history[s][1].zxid[1] # history[s][2].zxid[1]
                    \* /\ Cardinality(learners[s]) = 2
                    \* /\ state[t] = FOLLOWING /\ Len(history[t]) > 0 /\ lastCommitted[t].index > 0
                    )
\* DebugInv2 == CEPOCHmsgs = {}
\* DebugInv2 == NEWEPOCHmsgs = {}
DebugInv2 == ~(\E s,t \in Server : 
                    /\ s # t 
                    /\  currentEpoch[s] > currentEpoch[t]
                    /\ state[s] = LEADING /\ state[t] = LEADING
                    /\ zabState[s] = SYNCHRONIZATION
                    /\ \E ind \in DOMAIN history[t] : history[t][ind].zxid[1] < currentEpoch[s]
                )

\* If a node is currently leading 

\* DebugInv3 == TLCGet("level") < 80
\* DebugInv2 == \A m \in NEWLEADERmsgs : m.morder < 2

\* ShouldNotBeTriggered == \A p \in DOMAIN violatedInvariants: violatedInvariants[p] = FALSE

\* There is most one established leader for a certain epoch.
H_UniqueLeadership == \A i, j \in Server:
                        (/\ IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
                         /\ IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}
                         /\ currentEpoch[i] = currentEpoch[j]) => i = j

\* Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

\* PrefixConsistency: The prefix that have been committed 
\* in history in any process is the same.
H_PrefixConsistency == 
    \A i, j \in Server:
        LET smaller == Minimum({lastCommitted[i].index, lastCommitted[j].index}) IN
            (smaller > 0) =>
                /\ smaller \in DOMAIN history[i]
                /\ smaller \in DOMAIN history[j]
                /\ \A ind \in (DOMAIN history[i] \cap DOMAIN history[j]):
                    (ind <= smaller) => TxnEqual(history[i][ind], history[j][ind])

\* Integrity: If some follower delivers one transaction, then some primary has broadcast it.
\* Integrity == \A i \in Server:
\*                 /\ IsFollower(i)
\*                 /\ lastCommitted[i].index > 0
\*                 => \A idx \in 1..lastCommitted[i].index: \E proposal \in proposalMsgsLog:
\*                     LET txn_proposal == [ zxid  |-> proposal.zxid,
\*                                           value |-> proposal.data ]
\*                     IN  TxnEqual(history[i][idx], txn_proposal)

\* Agreement: If some follower f delivers transaction a and some follower f' delivers transaction b,
\*            then f' delivers a or f delivers b.
Agreement == \A i, j \in Server:
                /\ IsFollower(i) /\ lastCommitted[i].index > 0
                /\ IsFollower(j) /\ lastCommitted[j].index > 0
                =>
                \A idx1 \in 1..lastCommitted[i].index, idx2 \in 1..lastCommitted[j].index :
                    \/ \E idx_j \in 1..lastCommitted[j].index:
                        TxnEqual(history[j][idx_j], history[i][idx1])
                    \/ \E idx_i \in 1..lastCommitted[i].index:
                        TxnEqual(history[i][idx_i], history[j][idx2])

\* Total order: If some follower delivers a before b, then any process that delivers b
\*              must also deliver a and deliver a before b.
TotalOrder == \A i, j \in Server: 
                LET committed1 == lastCommitted[i].index 
                    committed2 == lastCommitted[j].index  
                IN committed1 >= 2 /\ committed2 >= 2
                    => \A idx_i1 \in 1..(committed1 - 1) : \A idx_i2 \in (idx_i1 + 1)..committed1 :
                    LET logOk == \E idx \in 1..committed2 :
                                     TxnEqual(history[i][idx_i2], history[j][idx])
                    IN \/ ~logOk 
                       \/ /\ logOk 
                          /\ \E idx_j2 \in 1..committed2 : 
                                /\ TxnEqual(history[i][idx_i2], history[j][idx_j2])
                                /\ \E idx_j1 \in 1..(idx_j2 - 1):
                                       TxnEqual(history[i][idx_i1], history[j][idx_j1])

\* Local primary order: If a primary broadcasts a before it broadcasts b, then a follower that
\*                      delivers b must also deliver a before b.
\* LocalPrimaryOrder == LET p_set(i, e) == {p \in proposalMsgsLog: /\ p.source = i 
\*                                                                 /\ p.epoch  = e }
\*                          txn_set(i, e) == { [ zxid  |-> p.zxid, 
\*                                               value |-> p.data ] : p \in p_set(i, e) }
\*                      IN \A i \in Server: \A e \in 1..currentEpoch[i]:
\*                          \/ Cardinality(txn_set(i, e)) < 2
\*                          \/ /\ Cardinality(txn_set(i, e)) >= 2
\*                             /\ \E txn1, txn2 \in txn_set(i, e):
\*                              \/ TxnEqual(txn1, txn2)
\*                              \/ /\ ~TxnEqual(txn1, txn2)
\*                                 /\ LET TxnPre  == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn2 ELSE txn1
\*                                        TxnNext == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn1 ELSE txn2
\*                                    IN \A j \in Server: /\ lastCommitted[j].index >= 2
\*                                                        /\ \E idx \in 1..lastCommitted[j].index: 
\*                                                             TxnEqual(history[j][idx], TxnNext)
\*                                         => \E idx2 \in 1..lastCommitted[j].index: 
\*                                             /\ TxnEqual(history[j][idx2], TxnNext)
\*                                             /\ idx2 > 1
\*                                             /\ \E idx1 \in 1..(idx2 - 1): 
\*                                                 TxnEqual(history[j][idx1], TxnPre)

\* Global primary order: A follower f delivers both a with epoch e and b with epoch e', and e < e',
\*                       then f must deliver a before b.
GlobalPrimaryOrder == \A i \in Server: lastCommitted[i].index >= 2
                         => \A idx1, idx2 \in 1..lastCommitted[i].index:
                                \/ ~EpochPrecedeInTxn(history[i][idx1], history[i][idx2])
                                \/ /\ EpochPrecedeInTxn(history[i][idx1], history[i][idx2])
                                   /\ idx1 < idx2

\* Primary integrity: If primary p broadcasts a and some follower f delivers b such that b has epoch
\*                    smaller than epoch of p, then p must deliver b before it broadcasts a.
PrimaryIntegrity == \A i, j \in Server: /\ IsLeader(i)   /\ IsMyLearner(i, j)
                                        /\ IsFollower(j) /\ IsMyLeader(j, i)
                                        /\ zabState[i] = BROADCAST
                                        /\ zabState[j] = BROADCAST
                                        /\ lastCommitted[j].index >= 1
                        => \A idx_j \in 1..lastCommitted[j].index:
                                \/ history[j][idx_j].zxid[1] >= currentEpoch[i]
                                \/ /\ history[j][idx_j].zxid[1] < currentEpoch[i]
                                   /\ \E idx_i \in 1..lastCommitted[i].index: 
                                        TxnEqual(history[i][idx_i], history[j][idx_j])


----------------------

\* Is log li a prefix of log lj.
IsPrefix(li,lj) == 
    /\ Len(li) <= Len(lj)
    /\ SubSeq(li, 1, Len(li)) = SubSeq(lj, 1, Len(li))

\* old_type: Seq(TXN) => Seq({zxid: ZXID, value: Int});
\* Extract only zxid and value from a given history.
\* TxnHistory(h) == FunAsSeq([i \in DOMAIN h |-> [zxid |-> h[i].zxid, value |-> h[i].value] ], Cardinality(DOMAIN h), Cardinality(DOMAIN h))

(**************

\* 
\* Helper lemma invariants
\* 


\* A leader is always a part of its own learner set.
H_LeaderInLearnerSet == \A i \in Server : IsLeader(i) => i \in learners[i]

\* If a NEWLEADER message has been sent from node N in epoch E, then N
\* must be LEADING in epoch E. Also, the receiver must be in learners[N].
H_NEWLEADERMsgSentByLeader == 
    \A i,j \in Server : 
        (PendingNEWLEADER(i,j)) => 
            /\ IsLeader(j) 
            /\ msgs[j][i][1].mepoch = currentEpoch[j]
            /\ i \in learners[j]
            /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}

*****)

\* START_PROOF

\* If a node is currently established leader in epoch E, it implies it has received a quorum of ACKE
\* responses from nodes.
H_EstablishedLeaderImpliesACKEQuorum == 
    \A i \in Server:
        (IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}) =>
            \E Q \in Quorums : 
            \A n \in Q :
            \E a \in ackeRecv[i] : 
                /\ a.sid = n
                /\ a.connected

\* H_NEWEPOCHImpliesQuorumSafeAtEpoch == 
\*     \A m \in NEWEPOCHmsgs : 
\*         \E Q \in Quorums : \A n \in Q : acceptedEpoch[n] >= m.mepoch

H_NodeCantSendCEPOCHToDifferentLeaders == 
    \A s,t \in Server : 
        IsLeader(s) /\ IsLeader(t) => 
        (\A cs \in cepochRecv[s] :
         \A ct \in cepochRecv[t] :
            ~(cs.epoch = ct.epoch /\ cs.sid = ct.sid /\ s # t))

H_UniqueEstablishedLeaderImpliesNEWEPOCHsFromThem == 
    \A m \in NEWEPOCHmsgs :
    \A i \in Server:
        ( /\ IsLeader(i) 
          /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}) => 
            /\ m.mepoch <= acceptedEpoch[i]
            /\ m.mepoch = acceptedEpoch[i] => m.msrc = i

\* If there is an established leader, there mustn't be a quorum of nodes that
\* sent ACKE to a different node.
H_UniqueEstablishedLeaderImpliesSafeAtEpoch == 
    \A i, j \in Server:
        ( /\ IsLeader(i) 
          /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST} 
          /\ i # j) =>
            /\ \* No other leader can be prepared to receive a quorum of ACKEs.
                LET ackeJ == {av.sid : av \in {a \in ackeRecv[j] : TRUE}} IN
                ~\E m \in ACKEPOCHmsgs : 
                    /\ m.mdst = j
                    /\ (ackeJ \in Quorums) \/ (ackeJ \cup {m.msrc} \in Quorums)
            /\ \E Q \in Quorums : \A n \in Q : acceptedEpoch[n] >= acceptedEpoch[i]

\* ACKEPOCH messages sent must be consistent with the CEPOCH quorum that a leader received recorded.
H_ACKEPOCHMsgsOnlyMustMatchRecv == 
    \A i, j \in Server:
        (IsLeader(i) 
        /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST} 
        /\ i # j) =>
            /\ \A m \in ACKEPOCHmsgs : 
                /\ m.mdst = i
                /\ \E c \in cepochRecv[i] : c.sid = m.msrc
            \* Two leaders cannot have recorded CEPOCHs from the same node.
            \* /\ IsLeader(j) => \A cj \in cepochRecv[j] : \A ci \in cepochRecv[i] : ci.sid # cj.sid

\* If a node is currently an established leader, then there can be no other currently active,
\* established leaders.
H_UniqueEstablishedLeader == 
    \A i, j \in Server:
        (IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST} /\ i # j) =>
            /\ ~(IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST})

\* If a NEWLEADER message has been sent from a leader N in epoch E, then 
\* that message's history must be a prefix of the leader's history in epoch E, w.r.t the txns
\* that appear in that history i.e. (zxid, value) pairs.
H_NEWLEADERMsgHistAndStateInv ==
    \A m \in NEWLEADERmsgs :
    \* \A i,j \in Server : 
        \* (PendingNEWLEADER(i,j)) => 
        \* /\ IsPrefix(TxnHistory(m.mhistory), TxnHistory(history[m.msrc]))
        \* Is prefix.
        /\ Len(m.mhistory) <= Len(history[m.msrc])
        /\ \A i \in DOMAIN m.mhistory : 
                /\ m.mhistory[i].zxid = history[m.msrc][i].zxid
                /\ m.mhistory[i].value = history[m.msrc][i].value
        /\ IsLeader(m.msrc) 
        /\ m.mepoch = currentEpoch[m.msrc]
        /\ m.mdst \in learners[m.msrc]
        /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}

H_LeaderInDISCOVERYImpliesNoCOMMITs == 
    \A s \in Server : 
    \A m \in COMMITmsgs :
        (IsLeader(s) /\ zabState[s] = DISCOVERY) => m.msrc # s

H_NEWLEADERIncomingImpliesNoIncomingCOMMIT == 
    \A m \in NEWLEADERmsgs :
        /\ ~\E mc \in COMMITmsgs : mc.mdst = m.mdst
        \* If you have an outstanding NEWLEADER, you can't have sent an ACKLD to that leader yet.
        /\ ~\E ackld \in ACKLDmsgs : ackld.msrc = m.mdst
        /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}
        /\ IsLeader(m.msrc) 
        /\ m.mdst \in learners[m.msrc]


H_PROPOSEIncomingImpliesNoACKEPOCH == 
    \A m \in PROPOSEmsgs :
        /\ ~\E mc \in ACKEPOCHmsgs : mc.msrc = m.mdst
        /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}
        /\ IsLeader(m.msrc) 
        /\ m.mdst \in learners[m.msrc]

H_NEWLEADERIncomingImpliesNoACKEPOCH == 
    \A m \in NEWLEADERmsgs :
        /\ ~\E mc \in ACKEPOCHmsgs : mc.msrc = m.mdst
        /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}
        /\ IsLeader(m.msrc) 
        /\ m.mdst \in learners[m.msrc]

H_NEWLEADERIncomingImpliesLastCommittedBound == 
    \A m \in NEWLEADERmsgs :
    \* \A i,j \in Server : 
        \* PendingNEWLEADER(i,j) => 
            (\* lastCommitted on node is <= length of incoming history.
             /\ lastCommitted[m.mdst].index <= Len(m.mhistory))
            \*  /\ IsFollower(m.mdst)
            \*  /\ IsLeader(m.msrc)
            \*  /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}

\* If a COMMIT message has been sent by a node, then the zxid referred to by that COMMIT
\* must be present in the sender's history, and its lastCommitted must cover that zxid in its history.
H_COMMITSentByNodeImpliesZxidInLog == 
    \A m \in COMMITmsgs :
        \E idx \in DOMAIN history[m.msrc] : 
            /\ history[m.msrc][idx].zxid = m.mzxid  
            /\ lastCommitted[m.msrc].index >= idx
            \* /\ state[m.mdst] \in {FOLLOWING}
            /\ state[m.msrc] = LEADING
            /\ zabState[m.msrc] = BROADCAST
            \* /\ m.msrc \in learners[m.msrc]
            \* /\ m.mdst \in learners[m.msrc]

\* If an ACK message exists from S for a given zxid, then that zxid must be present in the sender's history.
H_ACKMsgImpliesZxidInLog == 
    \A m \in ACKmsgs :
        /\ state[m.msrc] = FOLLOWING
        /\ connectInfo[m.msrc] = m.mdst
        /\ state[m.mdst] = LEADING 
        /\ m.mdst \in learners[m.mdst]
        /\ \E idx \in DOMAIN history[m.msrc] :  history[m.msrc][idx].zxid = m.mzxid
        \* Will also be present in the history of the leader receiving the ACK.
        /\ \E idx \in DOMAIN history[m.mdst] :  history[m.mdst][idx].zxid = m.mzxid


\* AllMsgs == UNION {{msgs[i][j][mi] : mi \in DOMAIN msgs[i][j]} : <<i,j>> \in Server \X Server}
\* MsgsWithHistoryZxids == 
    \* {m \in AllMsgs : (m.mtype = PROPOSE) \/ ("mhistory" \in DOMAIN m)}

\* @type: Set({zxid: ZXID, value: Int, epoch: Int, ackSid: Set(SERVER)});
PROPOSEZxids == {[zxid |-> m.mzxid, value |-> m.mdata, epoch |-> 0, ackSid |-> {} ] : m \in PROPOSEmsgs}
\* @type: Set({zxid: ZXID, value: Int, epoch: Int, ackSid: Set(SERVER)});
ACKEPOCHZxids == UNION {{[zxid |-> m.mhistory[i].zxid, value |-> m.mhistory[i].value, epoch |-> 0, ackSid |-> {}] : i \in DOMAIN m.mhistory} : m \in ACKEPOCHmsgs}
\* @type: Set({zxid: ZXID, value: Int, epoch: Int, ackSid: Set(SERVER)});
NEWLEADERZxids == UNION {{[zxid |-> m.mhistory[i].zxid, value |-> m.mhistory[i].value, epoch |-> 0, ackSid |-> {}] : i \in DOMAIN m.mhistory} : m \in NEWLEADERmsgs}  

\* @type: Set({zxid: ZXID, value: Int, epoch: Int, ackSid: Set(SERVER)});
MsgZxids == PROPOSEZxids \cup ACKEPOCHZxids \cup NEWLEADERZxids

TxnWithSameZxidEqualBetweenAllMessages == 
     \A txn,txn2 \in MsgZxids : 
        ZxidEqual(txn.zxid, txn2.zxid) => txn.value = txn2.value   

TxnZxidUniqueBetweenLocalHistoryAndMessages ==
    \A s \in Server :
    \A ind \in DOMAIN history[s] :
    \A txn \in MsgZxids : 
        ZxidEqual(txn.zxid, history[s][ind].zxid) => txn.value = history[s][ind].value

\* Any two transactions with the same zxid must be equal.
\* Note: this must hold no matter where a zxid appears i.e. in a message or on a local node.
TxnWithSameZxidEqual == 
    \A i,j \in Server : 
        \A idxi \in (DOMAIN history[i]) :
        \A idxj \in (DOMAIN history[j]) : 
            ZxidEqual(history[i][idxi].zxid, history[j][idxj].zxid) =>
                TxnEqual(history[i][idxi], history[j][idxj])

\* Transaction zxids are unique throughout local histories and all messages.
H_TxnZxidsUniqueHistoriesAndMessages == 
    /\ TxnWithSameZxidEqual
    /\ TxnWithSameZxidEqualBetweenAllMessages
    /\ TxnZxidUniqueBetweenLocalHistoryAndMessages
    \* Added for COI computation.
    /\ Cardinality(PROPOSEmsgs) >=0 /\ Cardinality(ACKEPOCHmsgs) >= 0 /\ Cardinality(NEWLEADERmsgs) >= 0


\* If a history entry is covered by some lastCommitted, then it must be present in 
\* the initial history as determined by a received quorum of ACKEPOCH messages.
H_CommittedEntryExistsInACKEPOCHQuorumHistory ==
    \A s \in Server : 
    \A idx \in DOMAIN history[s] : 
    \A m \in ACKEPOCHmsgs :
        \* Server i is a leader who is about to receive an ACK-E quorum and compute the new initial history.
        \* This initial history must contain the committed entry. 
        LET ackeRecvUpdated == [ackeRecv EXCEPT ![m.mdst] = UpdateAckeRecv(@, m.msrc, m.mepoch, m.mhistory) ] IN
            (
                \* Entry is covered by lastCommitted on s.
                /\ idx <= lastCommitted[s].index
                /\ zabState[m.mdst] \in {ELECTION, DISCOVERY, SYNCHRONIZATION}
                /\ state[m.mdst] = LEADING
                /\ IsQuorum({a.sid: a \in ackeRecvUpdated[m.mdst]})
            ) => 
                LET initHistory == DetermineInitialHistoryFromArg(ackeRecvUpdated, m.mdst) IN
                \E k \in DOMAIN initHistory : 
                    /\ k = idx
                    /\ TxnEqual(history[s][idx], initHistory[k])


COMMITLDSentByNodeImpliesZxidCommittedInLog == 
    \A m \in COMMITLDmsgs :
        (~ZxidEqual(m.mzxid, <<0,0>>)) => 
            /\ \E idx \in DOMAIN history[m.msrc] : 
                    /\ history[m.msrc][idx].zxid = m.mzxid  
                    /\ lastCommitted[m.msrc].index >= idx
            /\ state[m.msrc] = LEADING
            /\ state[m.mdst] = FOLLOWING
            /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}
            /\ zabState[m.mdst] \in {SYNCHRONIZATION}

ACKLDSentByNodeImpliesZxidCommittedInLog == 
    \A m \in ACKLDmsgs :
        (\/ (~ZxidEqual(m.mzxid, <<0,0>>)) ) => 
            /\ \E idx \in DOMAIN history[m.msrc] : history[m.msrc][idx].zxid = m.mzxid  
                    \* /\ lastCommitted[m.msrc].index >= idx
            /\ state[m.mdst] = LEADING
            /\ state[m.msrc] = FOLLOWING
            /\ zabState[m.mdst] \in {SYNCHRONIZATION, BROADCAST}
            /\ zabState[m.msrc] \in {SYNCHRONIZATION}

\* \* If a COMMITLD message has been sent by a node, then the zxid in this message must be committed 
\* \* in the sender's history.
H_COMMITLDSentByNodeImpliesZxidCommittedInLog == 
    /\ COMMITLDSentByNodeImpliesZxidCommittedInLog
    /\ ACKLDSentByNodeImpliesZxidCommittedInLog


\* If an entry is committed, then it should be contained in a leader's history.
H_CommittedEntryExistsInLeaderHistory == 
    \A i,j \in Server : 
        \A idx \in DOMAIN history[i] : 
            (/\ idx <= lastCommitted[i].index
             /\ IsLeader(j)
             /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}) => 
                \* Committed entry exists in leader's history.
                \E idx2 \in DOMAIN history[j] : 
                    /\ idx2 = idx
                    /\ history[j][idx2].zxid = history[i][idx].zxid

\* A node's lastCommitted index must always be <= its history length.
H_NodeHistoryBoundByLastCommittedIndex == 
    \A s \in Server : lastCommitted[s].index <= Len(history[s])

LeaderInBroadcastImpliesAllACKEPOCHorNEWLEADEREntriesInEpoch == 
    \A i \in Server :
    \A mhist \in ({ma.mhistory : ma \in ACKEPOCHmsgs} \cup {ma.mhistory : ma \in NEWLEADERmsgs}) :
    \A ind \in DOMAIN mhist :
        (/\ IsLeader(i)
         /\ zabState[i] \in {BROADCAST, SYNCHRONIZATION}
         /\ mhist[ind].zxid[1] = currentEpoch[i]) => 
            \E idx2 \in DOMAIN history[i] : ZxidEqual(history[i][idx2].zxid, mhist[ind].zxid)

LeaderInBroadcastImpliesAllAckERecvEntriesInEpoch == 
    \A i \in Server :
    \A j \in Server :
    \A acke \in ackeRecv[j] :
    \A ai \in DOMAIN acke.peerHistory :
        (/\ IsLeader(i)
         /\ zabState[i] \in {BROADCAST, SYNCHRONIZATION}
         /\ acke.peerHistory[ai].zxid[1] = currentEpoch[i]) => 
            \E idx2 \in DOMAIN history[i] : ZxidEqual(history[i][idx2].zxid, acke.peerHistory[ai].zxid)

\* Leader in BROADCAST phase must contain all history entries created in its epoch.
LeaderInBroadcastImpliesAllHistoryEntriesInEpoch == 
    \A i,j \in Server : 
    \A idx \in DOMAIN history[j] :
        (/\ IsLeader(i)
         /\ zabState[i] \in {BROADCAST, SYNCHRONIZATION}
         /\ history[j][idx].zxid[1] = currentEpoch[i]) => 
            \* Entry is in leader's history.
            \E idx2 \in DOMAIN history[i] : ZxidEqual(history[i][idx2].zxid, history[j][idx].zxid)

H_LeaderInBroadcastImpliesHasAllEntriesInEpoch ==
    /\ LeaderInBroadcastImpliesAllACKEPOCHorNEWLEADEREntriesInEpoch 
    /\ LeaderInBroadcastImpliesAllAckERecvEntriesInEpoch
    /\ LeaderInBroadcastImpliesAllHistoryEntriesInEpoch

H_ACKEPOCHImpliesSenderSafeAtEpoch == 
    /\ \A m \in ACKEPOCHmsgs : 
        acceptedEpoch[m.msrc] >= m.mepoch
    /\ \A s \in Server : \A a \in ackeRecv[s] : acceptedEpoch[a.sid] >= a.peerLastEpoch

H_EstablishedLeaderImpliesSafeAtCurrentEpoch == 
   \A i \in Server:
        ( /\ IsLeader(i) 
          /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}) =>
            /\ \E Q \in Quorums : \A n \in Q : acceptedEpoch[n] >= acceptedEpoch[i]


H_ACKLDImpliesNoNewACKEPOCHFromMe == 
    /\ \A i \in Server : 
        IsLeader(i) => 
            /\ \A mi \in ackldRecv[i] : 
                /\ ~\E ma \in ACKEPOCHmsgs : ma.msrc = mi.sid    
                /\ ~\E ma \in NEWLEADERmsgs : ma.mdst = mi.sid
    /\ \A m \in ACKLDmsgs :
        IsLeader(m.mdst) =>
            /\ IsFollower(m.msrc)
            /\ \A ma \in ACKEPOCHmsgs : ma.msrc # m.msrc 
            /\ \A ma \in NEWLEADERmsgs : ma.mdst # m.msrc 

\* If a leader is in BROADCAST, no NEWLEADER messages should be in-flight
H_LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight == 
    \A s \in Server : 
    (/\ state[s] = LEADING 
     /\ zabState[s] \in {BROADCAST}) => 
        (\A i,j \in Server :
            /\ ACKLDmsgs = {} 
            /\ NEWLEADERmsgs = {}
            /\ \A m \in ACKEPOCHmsgs : m.mdst = s
            /\ \A m \in NEWEPOCHmsgs : m.msrc = s
            /\ \A m \in CEPOCHmsgs : m.mdst = s
        )


\* Zxids across peer history at all nodes.
TxnWithSameZxidEqualInPeerHistory == 
    \A s,t \in Server :
    \A x \in ackeRecv[s] :
    \A y \in ackeRecv[t] :
        \A ix \in DOMAIN x.peerHistory :
        \A iy \in DOMAIN y.peerHistory :
            ZxidEqual(x.peerHistory[ix].zxid, y.peerHistory[iy].zxid) =>
                TxnEqual(x.peerHistory[ix], y.peerHistory[iy])

TxnWithSameZxidEqualLocalToPeerHistory == 
    \A s \in Server :
    \A x \in ackeRecv[s] :
    \A i \in Server : 
    \A idxi \in (DOMAIN history[i]) :
        \A ix \in DOMAIN x.peerHistory :
            ZxidEqual(x.peerHistory[ix].zxid, history[i][idxi].zxid) =>
                TxnEqual(x.peerHistory[ix], history[i][idxi])

TxnWithSameZxidEqualMsgsToPeerHistory == 
    \A s \in Server :
    \A x \in ackeRecv[s] :
    \A txn \in MsgZxids :
        \A ix \in DOMAIN x.peerHistory :
            ZxidEqual(x.peerHistory[ix].zxid, txn.zxid) =>
                TxnEqual(x.peerHistory[ix], txn)

\* Covering zxid equality within peer history and local history.
H_TxnWithSameZxidEqualPeerHistory == 
    /\ TxnWithSameZxidEqualInPeerHistory
    /\ TxnWithSameZxidEqualLocalToPeerHistory
    /\ TxnWithSameZxidEqualMsgsToPeerHistory

\* If a PROPOSE message has been sent with a particular zxid, then this zxid must be present
\* in the sender's log, and the sender must be a leader.
H_PROPOSEMsgSentByNodeImpliesZxidInLog == 
    \* \A i,j \in Server : 
    \A m \in PROPOSEmsgs :
        \* (PendingPROPOSE(i,j)) => 
            /\ IsLeader(m.msrc)
            /\ zabState[m.msrc] = BROADCAST
            /\ m.mdst \in learners[m.msrc]
            /\ m.msrc \in learners[m.msrc]
            /\ \E idx \in DOMAIN history[m.msrc] : history[m.msrc][idx].zxid = m.mzxid

H_ACKERecvPeerHistoryContainedInSender == 
    \A s \in Server :
    IsLeader(s) => 
        \A a \in ackeRecv[s] :  
            /\ a.sid # s => IsFollower(a.sid)
            /\ \A ind \in DOMAIN a.peerHistory : 
                /\ Len(history[a.sid]) >= ind
                /\ TxnEqual(history[a.sid][ind], a.peerHistory[ind])
                \* /\ m.mhistory[ind].zxid = history[m.msrc][ind].zxid
                \* /\ m.mhistory[ind].value = history[m.msrc][ind].value
        \* a.peerHistory
        \* /\ state[m.msrc] = FOLLOWING
        \* /\ state[m.mdst] = LEADING
        \* /\ zabState[m.msrc] \in {SYNCHRONIZATION}
        \* /\ Len(m.mhistory) = Len(history[m.msrc])
        \* /\ \A ind \in DOMAIN m.mhistory : 
        \*     /\ m.mhistory[ind].zxid = history[m.msrc][ind].zxid
        \*     /\ m.mhistory[ind].value = history[m.msrc][ind].value

\* ACKEPOCH response history must be contained in the sender's history, who must
\* be a follower.
H_ACKEPOCHHistoryContainedInFOLLOWINGSender == 
    \A m \in ACKEPOCHmsgs :
        /\ state[m.msrc] = FOLLOWING
        /\ state[m.mdst] = LEADING
        /\ zabState[m.msrc] \in {SYNCHRONIZATION}
        /\ Len(m.mhistory) = Len(history[m.msrc])
        /\ \A ind \in DOMAIN m.mhistory : 
            /\ m.mhistory[ind].zxid = history[m.msrc][ind].zxid
            /\ m.mhistory[ind].value = history[m.msrc][ind].value

\* Leader in broadcast implies no NEWEPOCH messages in flight.
H_LeaderInBroadcastImpliesNoNEWEPOCHInFlight == 
    \A s \in Server : 
    ( /\ state[s] = LEADING 
      /\ zabState[s] \in {BROADCAST}) => 
        /\ \A m \in NEWEPOCHmsgs :
            /\ m.mepoch >= currentEpoch[s]
            /\ m.mepoch >= acceptedEpoch[s]
            /\ currentEpoch[s] <= acceptedEpoch[s]

H_PROPOSEMsgInFlightImpliesNodesInBROADCAST == 
    \A m \in PROPOSEmsgs :
        /\ zabState[m.msrc] = BROADCAST
        /\ zabState[m.mdst] \in {SYNCHRONIZATION, BROADCAST}
        /\ IsFollower(m.mdst)
        /\ IsLeader(m.msrc)
        /\ m.mdst \in learners[m.msrc]

\* If an ACK message is in flight, there must be a leader and they
\* are in BROADCAST.
H_ACKMsgInFlightImpliesNodesInBROADCAST == 
    \A i,j \in Server :
    \A m \in ACKmsgs : 
        \* (PendingACK(i,j)) =>
            /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}
            /\ zabState[m.mdst] = BROADCAST
            /\ IsFollower(m.msrc)
            /\ IsLeader(m.mdst)
            \* /\ NEWEPOCHmsgs = {}

H_CommittedEntryExistsInNEWLEADERHistory ==
    \A s \in Server : 
    \A idx \in DOMAIN history[s] : 
    \A m \in NEWLEADERmsgs :
        (idx <= lastCommitted[s].index) =>
            (\E idx2 \in DOMAIN m.mhistory : 
                /\ idx2 = idx
                /\ TxnEqual(history[s][idx], m.mhistory[idx2]))

\* Any committed entry exists in the history of some quorum of servers.
H_CommittedEntryExistsOnQuorum ==
    \A s \in Server : 
    \A idx \in DOMAIN history[s] : 
        \* An entry is covered by lastCommitted on s.
        (idx <= lastCommitted[s].index) =>
            \E Q \in Quorums : 
            \A n \in Q : 
                \E ic \in DOMAIN history[n] : 
                    /\ ic = idx
                    /\ TxnEqual(history[s][idx], history[n][ic])

ZxidExistsOnQuorum(zxid) == 
  \E Q \in Quorums : 
    \A n \in Q : 
    \E ic \in DOMAIN history[n] : 
        history[n][ic].zxid = zxid 

\* If an ACKLD message exists from S for a given zxid, then that zxid must be present in the sender's history.
\* Also, this zxid should exist on a quorum (?), since it must be committed?
H_ACKLDMsgImpliesZxidInLog == 
    \A m \in ACKLDmsgs :
        (ZxidCompare(m.mzxid, <<0,0>>)) => 
            /\ \E idx \in DOMAIN history[m.msrc] : history[m.msrc][idx].zxid = m.mzxid
            \* Entry exists on a quorum, since it must be committed.
            /\ ZxidExistsOnQuorum(m.mzxid)
            /\ state[m.msrc] = FOLLOWING
            /\ state[m.mdst] = LEADING
            /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}
            /\ zabState[m.mdst] \in {SYNCHRONIZATION, BROADCAST}

\* NEWLEADER history exists on a quorum.
\* WRONG!
H_NEWLEADERHistoryExistsOnQuorum == 
    \A m \in NEWLEADERmsgs :
    (/\ IsLeader(m.msrc) 
     /\ zabState[m.msrc] \in {SYNCHRONIZATION, BROADCAST}) => 
        \A ih \in DOMAIN m.mhistory : 
            \E Q \in Quorums : 
            \A n \in Q : 
            \E ic \in DOMAIN history[n] : 
                /\ history[n][ic].zxid = m.mhistory[ih].zxid 
                \* /\ IsLeader(m.msrc)
            \* /\ acceptedEpoch[n] >= m.mepoch

\* If a follower has an incoming NEWEPOCH message, then this must be the only incoming message it
\* has?
\* H_NEWEPOCHMsgImpliesOnlyInBuffer == 
\*     \A i \in Server :
\*      IsFollower(i) =>
\*     \A m \in NEWEPOCHmsgs :
\*         (m.mdst = i) =>
\*             \A cem \in CEPOCHmsgs : cem.dst # i  
 
H_NodeLOOKINGImpliesNoIncomingCEPOCH ==
    \A i \in Server : 
        (state[i] = LOOKING) => 
            /\ \A m \in CEPOCHmsgs : ~(m.mdst =i \/ m.msrc = i)
            /\ (zabState[i] \in {ELECTION, DISCOVERY})
            \* /\ \A c \in cepochRecv[i] : c.sid = i

H_NodeLOOKINGImpliesNoIncomingNEWEPOCH ==
    \A i \in Server : 
        (state[i] = LOOKING) => 
            /\ \A m \in NEWEPOCHmsgs : ~(m.mdst =i \/ m.msrc = i)
            /\ (zabState[i] \in {ELECTION, DISCOVERY})
            /\ ~\E j \in Server : IsLeader(j) /\ i \in learners[j]


H_NodeLOOKINGImpliesNoIncomingACKEPOCH ==
    \A i \in Server : 
        (state[i] = LOOKING) => 
            /\ \A m \in ACKEPOCHmsgs : ~(m.mdst =i)
            /\ (zabState[i] \in {ELECTION, DISCOVERY})

\* If a node is LOOKING, then it must have an empty input buffer.
H_NodeLOOKINGImpliesEmptyInputBuffer == 
    \A i \in Server : 
        (state[i] = LOOKING) => 
            \* /\ \A m \in CEPOCHmsgs : ~(m.mdst =i)
            \* /\ \A m \in NEWEPOCHmsgs : ~(m.mdst =i)
            \* /\ \A m \in NEWLEADERmsgs : ~(m.mdst =i)
            \* /\ \A m \in ACKEPOCHmsgs : ~(m.mdst =i)
            \* /\ \A m \in ACKLDmsgs : ~(m.mdst =i)
            \* /\ \A m \in COMMITLDmsgs : ~(m.mdst =i)
            \* /\ \A m \in PROPOSEmsgs : ~(m.mdst =i)
            \* /\ \A m \in ACKmsgs : ~(m.mdst =i)
            \* /\ \A m \in COMMITmsgs : ~(m.mdst =i)
            /\ (zabState[i] \in {ELECTION, DISCOVERY})
            \* a node in LOOKING shouldn't exist as a learner of any leader.
            /\ ~\E j \in Server : IsLeader(j) /\ i \in learners[j]

\* If a node is LOOKING, then it must be in DISCOVERY or ELECTION and have an empty input buffer.
H_NodeLOOKINGImpliesELECTIONorDISCOVERY == 
    \A i \in Server : (state[i] = LOOKING) => (zabState[i] \in {ELECTION, DISCOVERY})

H_FollowersHaveNoMessagesSentToSelf == 
    \A s \in Server : 
        (IsFollower(s) \/ IsLooking(s)) =>  
            /\ \A m \in CEPOCHmsgs : (m.mdst # m.msrc)
            /\ \A m \in NEWEPOCHmsgs : (m.mdst # m.msrc)
            /\ \A m \in NEWLEADERmsgs : (m.mdst # m.msrc)
            /\ \A m \in ACKEPOCHmsgs : (m.mdst # m.msrc)
            /\ \A m \in ACKLDmsgs : (m.mdst # m.msrc)
            /\ \A m \in COMMITLDmsgs : (m.mdst # m.msrc)
            /\ \A m \in PROPOSEmsgs : (m.mdst # m.msrc)
            /\ \A m \in ACKmsgs : (m.mdst # m.msrc)
            /\ \A m \in COMMITmsgs : (m.mdst # m.msrc)

H_CEPOCHRecvsAreLearners == 
    \A s \in Server : 
        IsLeader(s) => 
            /\ \E c \in cepochRecv[s] : c.sid = s
            /\ \A c \in cepochRecv[s] :
                \*  /\ (c.sid # s) => IsFollower(c.sid) 
                 /\ (c.sid \in learners[s])

H_NodeLOOKINGImpliesNotInOtherCEPOCHRecv == 
    \A i,j \in Server :
        (IsLeader(j) /\ state[i] = LOOKING /\ i # j) => 
            \A c \in cepochRecv[j] : c.sid # i

H_LeaderCEPOCHMsgsUnique == 
    \A i,j \in Server :
        \* \* Nodes don't send CEPOCH to different leaders.
        /\ \A mi,mj \in CEPOCHmsgs : ~(mi.msrc = mj.msrc /\ mi.mdst # mj.mdst)

H_LeaderCEPOCHRecvsUnique == 
    \A i,j \in Server :
        \* If a CEPOCH msg is outstanding, a different leader can't have recorded such a CEPOCH.
        /\ \A m \in CEPOCHmsgs : 
            /\ IsLeader(m.mdst)
            /\ IsLeader(j) => ~\E c \in cepochRecv[j] : c.sid = m.msrc /\ m.mdst # j
            /\ m.msrc \in learners[m.mdst]
            /\ IsFollower(m.msrc)

H_TwoLeadersCantHaveSameCEPOCH ==
    \A i,j \in Server :
        \* Two leaders cannot have recorded CEPOCHs from the same node.
        /\ (IsLeader(i) /\ IsLeader(j) /\ i # j) => 
             /\ \A cj \in cepochRecv[j] : \A ci \in cepochRecv[i] : ci.sid # cj.sid
            \*  /\ \A ci \in cepochRecv[i] : ci.sid # i => IsFollower(ci.sid)


H_ACKEPOCHFromNodeImpliesCEPOCHRecvd == 
    \A m \in ACKEPOCHmsgs : 
        /\ IsLeader(m.mdst)
        /\ \E c \in cepochRecv[m.mdst] : c.sid = m.msrc

H_NEWEPOCHFromNodeImpliesLEADING ==
    \A m \in NEWEPOCHmsgs :
        /\ IsLeader(m.msrc)
        /\ \E c \in cepochRecv[m.msrc] : c.sid = m.mdst


\* AckLDRecvServers(i) == {v.sid : v \in {a \in ackldRecv[i]: TRUE }}
AckLDRecvServers(i) == {a.sid : a \in ackldRecv[i]}


H_AckLDRecvsAreConnected == 
    \A s \in Server : IsLeader(s) => (\A a \in ackldRecv[s] : a.connected = TRUE)

H_LeaderInBROADCASTImpliesAckLDQuorum == 
    \A i,j \in Server : 
        (/\ IsLeader(i) 
         /\ zabState[i] = BROADCAST) => 
            /\ AckLDRecvServers(i) \in Quorums
            \* Should have gotten ACKLD responses back only from your learners.
            /\ AckLDRecvServers(i) \subseteq learners[i]

\* If an ACKLD is pending from a follower to a leader, then
\* that follower must have no other outstanding messages.
H_ACKLDMsgSentByFollowerImpliesEmptyBuffer == 
    \A i,j \in Server : 
    \A m \in ACKLDmsgs : 
        \* (PendingACKLD(i,j)) => 
            /\ ~(m.msrc = i /\ m.mdst = j) 
            /\ state[m.msrc] = FOLLOWING

H_FollowerCantBeLearnerToDifferentLeaders == 
    \A i,la,lb \in Server : 
        (\*/\ \*(IsFollower(i) \/ IsLooking(i))
         /\ IsLeader(la)
         /\ IsLeader(lb)
         /\ la # lb) => 
            ~(i \in learners[la] /\ i \in learners[lb])

H_LeaderContainsSelfAsLearner == 
    \A s \in Server : IsLeader(s) => s \in learners[s]

H_LeaderImpliesNotInELECTION == 
    \A s \in Server : IsLeader(s) => zabState[s] \notin {ELECTION}

H_LeaderImpliesLearnersFollowing == 
    \A i \in Server :
    (/\ IsLeader(i) 
     /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
     ) =>
        /\ \A j \in learners[i] : i # j => state[j] # LEADING

H_LeaderInBROADCASTImpliesLearnerInBROADCAST == 
    \A i,j \in Server : 
        (/\ IsLeader(i) 
         /\ zabState[i] \in {DISCOVERY, SYNCHRONIZATION, BROADCAST}) =>   
            /\ i \in learners[i]
            /\ (\A a \in ackeRecv[i] :
                (a.connected /\ a.sid # i /\ a.sid \in learners[i]) => 
                    /\ IsFollower(a.sid)
                    /\ zabState[a.sid] \in {SYNCHRONIZATION, BROADCAST})


H_NEWLEADERHistoryAtLeastNewerThanACKEPOCHs ==
    \A m \in NEWLEADERmsgs : 
    \A mae \in ACKEPOCHmsgs :
        \/ ZxidCompare(LastZxidOfHistory(m.mhistory),LastZxidOfHistory(mae.mhistory))
        \/ ZxidEqual(LastZxidOfHistory(m.mhistory),LastZxidOfHistory(mae.mhistory))


(******





\* TODO: Work on this further to develop a more unified lemma for establishing zxid uniqueness throughout the whole system.
\* All messages currently in the system
AllMsgs == UNION {{msgs[i][j][mi] : mi \in DOMAIN msgs[i][j]} : <<i,j>> \in Server \X Server}

\* AllACKs == {m \in AllMsgs : m.mtype = "ACK"}

\* \* Set of all [zxid: zxid, value: value) records/pairs that exist in the system. 
\* AllSystemsZxids == 
\*     UNION { TxnHistory(history[i]) : i \in Server } \cup
\*     {m.mzxid}

MsgsWithHistoryZxids == 
    {m \in AllMsgs : (m.mtype = PROPOSE) \/ ("mhistory" \in DOMAIN m)}

MsgZxids == 
    UNION {IF m.mtype = PROPOSE
                            THEN {[zxid |-> m.mzxid, value |-> m.mdata]}
                            ELSE {[zxid |-> m.mhistory[i].zxid, value |-> m.mhistory[i].value] : i \in DOMAIN m.mhistory} : 
                            m \in MsgsWithHistoryZxids}

\* If zxid matches between any two histories in messages in network, 
\* then the transactions must be equal.
\* H_TxnWithSameZxidEqualInMessages == 
\*     \A i,j,i2,j2 \in Server :
\*         \A idx \in DOMAIN msgs[i][j] : 
\*         \A idx2 \in DOMAIN msgs[i2][j2] : 
\*             (/\ "mhistory" \in DOMAIN msgs[i][j][idx]
\*              /\ "mhistory" \in DOMAIN msgs[i2][j2][idx2]) =>
\*                 \A h1 \in DOMAIN msgs[i][j][idx].mhistory :
\*                 \A h2 \in DOMAIN msgs[i2][j2][idx2].mhistory : 
\*                     ZxidEqual(msgs[i][j][idx].mhistory[h1].zxid, msgs[i2][j2][idx2].mhistory[h2].zxid) =>
\*                     TxnEqual(msgs[i][j][idx].mhistory[h1], msgs[i2][j2][idx2].mhistory[h2])

\* H_TxnWithSameZxidEqualInPROPOSEMessages == 
\*     \A i,j,i2,j2 \in Server :
\*     \A idx \in (DOMAIN msgs[i][j]) : 
\*     \A idx2 \in (DOMAIN msgs[i2][j2]) : 
\*         (/\ msgs[i][j][idx].mtype = PROPOSE 
\*          /\ msgs[i2][j2][idx2].mtype = PROPOSE) =>
\*             (ZxidEqual(msgs[i][j][idx].mzxid, msgs[i2][j2][idx2].mzxid) => 
\*                 (msgs[i][j][idx].mdata = msgs[i2][j2][idx2].mdata))

\* H_TxnWithSameZxidEqualBetweenLocalHistoryAndMessages == 
\*     \A i,j,i1 \in Server :
\*         \A idx \in DOMAIN msgs[i][j] : 
\*         \A idx2 \in DOMAIN history[i1] : 
\*             (/\ "mhistory" \in DOMAIN msgs[i][j][idx]) =>
\*                 \A h1 \in DOMAIN msgs[i][j][idx].mhistory :
\*                 \A h2 \in DOMAIN history[i1]: 
\*                     ZxidEqual(msgs[i][j][idx].mhistory[h1].zxid, history[i1][h2].zxid) =>
\*                     TxnEqual(msgs[i][j][idx].mhistory[h1], history[i1][h2])

\* H_TxnWithSameZxidEqualBetweenLocalHistoryAndPROPOSEMessages == 
\*     \A i,j,i1 \in Server :
\*         \A idx \in DOMAIN msgs[i][j] : 
\*         \A idx2 \in DOMAIN history[i1] : 
\*             (msgs[i][j][idx].mtype = PROPOSE) =>
\*                 \A h2 \in DOMAIN history[i1] : 
\*                     ZxidEqual(msgs[i][j][idx].mzxid, history[i1][h2].zxid) =>
\*                     msgs[i][j][idx].mdata = history[i1][h2].value



H_ServerInEntryAckSidImpliesHasEntry == 
    \A s,t \in Server : 
    \A ind \in DOMAIN history[s]:
        (state[s] = LEADING /\ t \in history[s][ind].ackSid) =>
            \E indt \in DOMAIN history[t] : 
                TxnEqual(history[t][indt], history[s][ind])



\* TODO.
\* \* Leader implies all followers have no pending NEWEPOCH msgs.
\* H_LeaderImpliesNoPendingNEWEPOCHMsgs == 
\*     \A i,j \in Server : 
\*         (IsLeader(j) /\ zabState[j] = BROADCAST /\ j \in AckLDRecvServers(j)) => ~PendingNEWEPOCH(i,j)



\* The learner of a leader in BROADCAST must also be in BROADCAST and a follower.
\* H_LeaderInBROADCASTImpliesLearnerInBROADCAST == 
\*     \A i,j \in Server : 
\*         (/\ IsLeader(i) 
\*          /\ zabState[i] = BROADCAST
\*          /\ j \in learners[i] 
\*          /\ j # i ) => 
\*             \* /\ {a \in ackldRecv[i]: a.connected = TRUE } \in Quorums
\*             \* TODO: Think about this condition more.
\*             \* /\ (zabState[j] # BROADCAST) => msgs[i][j] # <<>>
\*             /\ IsFollower(j)



\* There must be a unique NEWLEADER message sent per epoch.
H_NEWLEADERUniquePerEpoch == 
    \A i,j \in Server : 
    \A i2,j2 \in Server :
        \A ind1 \in DOMAIN msgs[i][j] :
        \A ind2 \in DOMAIN msgs[i2][j2] :   
            (/\ msgs[i][j][ind1].mtype = NEWLEADER 
             /\ msgs[i2][j2][ind2].mtype = NEWLEADER
             /\ msgs[i2][j2][ind2].mepoch = msgs[i][j][ind1].mepoch) => 
                msgs[i][j][ind1] = msgs[i2][j2][ind2]

\* If a follower has sent ACKLD to a leader, then its log must match the leader's log.
H_ACKLDSentByFollowerImpliesLogMatch == 
    \A i,j \in Server : 
        (/\ PendingACKLD(i,j)
         /\ IsLeader(i)) => 
            IsPrefix(TxnHistory(history[j]), TxnHistory(history[i]))

\* If a leader is in DISCOVERY in epoch E, then no NEWLEADER messages could have been sent
\* from this leader in epoch E.
H_LeaderInDiscoveryImpliesNoNEWLEADERMsgs == 
    \A i,j \in Server : 
        (/\ (IsLeader(j) \/ IsLooking(j))
         /\ zabState[j] \in {DISCOVERY}) =>
             ~(PendingNEWLEADER(i,j) /\ msgs[j][i][1].mepoch = currentEpoch[j])

\* If an ACK-EPOCH quorum has been collected by a leader, then it must be in SYNCHRONIZATION.
H_ACKEPOCHQuorumImpliesLeaderInSYNCHRONIZATIONorBROADCAST == 
    \A i \in Server : 
        (/\ IsLeader(i)
         /\ IsQuorum({a.sid: a \in ackeRecv[i]})) => 
            zabState[i] \in {SYNCHRONIZATION, BROADCAST}

H_ACKEPOCHQuorumImpliesAcceptedEpochCorrect == 
    \A i \in Server : 
        (/\ IsLeader(i)
         /\ IsQuorum({a.sid: a \in ackeRecv[i]})) => 
            acceptedEpoch[i] = currentEpoch[i]

\* If a NEWLEADER message in epoch E has been sent, this must imply no log entries
\* in epoch E exist.
H_NEWLEADERMsgImpliesNoLogEntriesInEpoch == 
    \A i,j \in Server : 
    \A s \in Server :
    \A si \in DOMAIN history[s] : 
        PendingNEWLEADER(i,j) => 
            /\ state[j] = LEADING
            /\ state[i] = FOLLOWING
            /\ zabState[j] \in {SYNCHRONIZATION}
            /\ history[s][si].zxid[1] # msgs[j][i][1].mepoch

        \* (PendingNEWLEADER(i,j) /\ msgs[j][i][1].mepoch = currentEpoch[j]) => Len(history[j]) = 0

\* If a leader is in BROADCAST in epoch E, then there cannot be any NEWLEADER or ACKEPOCH messages in flight.
\* H_LeaderInBroadcastImpliesNoNEWLEADER == 
\*     \A s \in Server : 
\*         (state[s] = LEADING /\ zabState[s] = BROADCAST) => 
\*             (\A i,j \in Server :
\*              \A mi \in DOMAIN msgs[i][j] : 
\*                 msgs[i][j][mi].mtype \notin {NEWLEADER})

NonPROPOSEMsgs(i,j) == 
    [mi \in {x \in DOMAIN msgs[i][j] : msgs[i][j][x].mtype # PROPOSE} |-> msgs[i][j][mi]]

D2 == \A i,j \in Server : Cardinality(DOMAIN NonPROPOSEMsgs(i,j)) <= 5

Morder1 == 
    \A i,j \in Server : 
    \A mi,mj \in DOMAIN msgs[i][j] : 
        (mi < mj /\ msgs[i][j][mi].mtype = PROPOSE) => msgs[i][j][mj].mtype \notin {ACKLD, NEWEPOCH}



*********)


\* 
\* Apalache stuff.
\* 

CInit == 
    /\ MaxEpoch = 2
    /\ MaxHistLen = 1
    /\ Server = {"s1", "s2", "s3"}
    \* /\ Server = {"s1", "s2"}
    /\ CEPOCH = "CEPOCH"
    /\ NEWEPOCH = "NEWEPOCH"
    /\ NEWLEADER = "NEWLEADER"
    /\ ACKEPOCH = "ACKEPOCH"
    /\ ACKLD = "ACKLD"
    /\ COMMITLD = "COMMITLD"
    /\ PROPOSE = "PROPOSE"
    /\ ACK = "ACK"
    /\ COMMIT = "COMMIT"
    /\ DISCOVERY = "DISCOVERY"
    /\ ELECTION = "ELECTION"
    /\ BROADCAST = "BROADCAST"
    /\ SYNCHRONIZATION = "SYNCHRONIZATION"
    /\ LOOKING = "LOOKING"
    /\ FOLLOWING = "FOLLOWING"
    /\ LEADING = "LEADING"



\* SetOfHistsTypeBounded == RandomSetOfSubsets(5, 5, HistTypeBounded)

\* AckeRecvTypeBounded == 
\*     RandomSetOfSubsets(1, 1, [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: HistTypeBounded]) \cup
\*     RandomSetOfSubsets(2, 2, [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: HistTypeBounded])



ApaValue == {0,1}
Indices == 0..MaxHistLen

ApaZxidType == Epoch \X Indices

ApaHistEntryType == [zxid: ApaZxidType, value: ApaValue, ackSid: SUBSET Server, epoch: Epoch]

\* ApaHistTypeBounded == Gen(3)
    \* Seq(ApaHistEntryType)

ApaHistEntryTypeBoundLen1 == {<<>>} \cup {<<x>> : x \in ApaHistEntryType}

ApaMsgCEPOCHType == [mtype: {CEPOCH}, mepoch: Epoch, msrc:Server, mdst:Server, morder: {0}]
ApaMsgNEWEPOCHType == [mtype: {NEWEPOCH}, mepoch: Epoch,  msrc:Server, mdst:Server, morder: {0}]
ApaMsgACKEPOCHType == [mtype: {ACKEPOCH}, mepoch: Epoch, mhistory: ApaHistEntryTypeBoundLen1,  msrc:Server, mdst:Server, morder: {0}]
ApaMsgNEWLEADERType == [mtype: {NEWLEADER}, mepoch: Epoch, mhistory: ApaHistEntryTypeBoundLen1,  msrc:Server, mdst:Server, morder: {0}]
ApaMsgACKLDType == [mtype: {ACKLD}, mzxid: ApaZxidType, msrc:Server, mdst:Server, morder: {0}]
ApaMsgCOMMITLDType == [mtype: {COMMITLD}, mzxid: ApaZxidType, msrc:Server, mdst:Server, morder: {0}]
ApaMsgPROPOSEType == [mtype: {PROPOSE}, mzxid: ApaZxidType, mdata: ApaValue,  msrc:Server, mdst:Server]
ApaMsgACKType == [mtype: {ACK}, mzxid: ApaZxidType, msrc:Server, mdst:Server]
ApaMsgCOMMITType == [mtype: {COMMIT}, mzxid: ApaZxidType, msrc:Server, mdst:Server]

ApaCEpochRecvType == [sid: Server, connected: BOOLEAN, epoch: Epoch]

\* Gives a candidate TypeOK definition for all variables in the spec.
ApaTypeOK == 
    /\ state \in [Server -> {LOOKING, FOLLOWING, LEADING}]
    /\ zabState \in [Server -> {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}]
    /\ acceptedEpoch \in [Server -> Epoch]
    /\ currentEpoch \in [Server -> Epoch]
    /\ history = Gen(3)
    /\ \A s \in Server : \A i \in DOMAIN history[s] : history[s][i] \in ApaHistEntryType
    /\ \A s \in Server : Len(history[s]) <= MaxHistLen
    /\ DOMAIN history = Server
    /\ lastCommitted \in [Server -> [index: Indices, zxid: ApaZxidType]]
    /\ learners \in [Server -> SUBSET Server]
    /\ cepochRecv \in [Server -> SUBSET ApaCEpochRecvType]
    \* Assumes here that MaxHistLen=1 for now.
    /\ ackeRecv = Gen(3)
    /\ ackeRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN, peerLastEpoch: Epoch, peerHistory: ApaHistEntryTypeBoundLen1]]
    /\ ackldRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN]]
    /\ sendCounter \in [Server -> {0,1,2}]
    /\ connectInfo \in [Server -> Server]
    /\ leaderOracle \in Server
    /\ mesgs = [s \in Server |-> [v \in Server |-> << >>] ]
    /\ CEPOCHmsgs = Gen(5)
    /\ \A m \in CEPOCHmsgs : m \in ApaMsgCEPOCHType
    /\ NEWEPOCHmsgs = Gen(5)
    /\ \A m \in NEWEPOCHmsgs : m \in ApaMsgNEWEPOCHType
    /\ ACKEPOCHmsgs = Gen(5)
    /\ \A m \in ACKEPOCHmsgs : m \in ApaMsgACKEPOCHType
    \* /\ \A m \in ACKEPOCHmsgs : \A mi \in DOMAIN m.mhistory : m.mhistory[mi] \in ApaHistEntryType
    /\ NEWLEADERmsgs = Gen(6)
    /\ \A m \in NEWLEADERmsgs : m \in ApaMsgNEWLEADERType
    \* /\ \A m \in NEWLEADERmsgs : \A mi \in DOMAIN m.mhistory : m.mhistory[mi] \in ApaHistEntryType
    /\ ACKLDmsgs = Gen(5)
    /\ \A m \in ACKLDmsgs : m \in ApaMsgACKLDType
    /\ COMMITLDmsgs = Gen(5)
    /\ \A m \in COMMITLDmsgs : m \in ApaMsgCOMMITLDType
    /\ PROPOSEmsgs = Gen(5)
    /\ \A m \in PROPOSEmsgs : m \in ApaMsgPROPOSEType
    /\ ACKmsgs = Gen(4)
    /\ \A m \in ACKmsgs : m \in ApaMsgACKType
    /\ COMMITmsgs = Gen(4)
    /\ \A m \in COMMITmsgs : m \in ApaMsgCOMMITType
    \* /\ COMMITmsgs \in SUBSET ApaMsgCOMMITType

InvTest == 
    /\ ApaTypeOK
    /\ H_UniqueLeadership


\* DInv1 == ACKEPOCHmsgs = {}
DInv1 == ACKmsgs = {}
=============================================================================
\* Modification History
\* Last modified Tue Jan 31 20:40:11 CST 2023 by huangbinyu
\* Last modified Sat Dec 11 22:31:08 CST 2021 by Dell
\* Created Thu Dec 02 20:49:23 CST 2021 by Dell