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
EXTENDS Integers, FiniteSets, Sequences, Naturals, TLC, Randomization
-----------------------------------------------------------------------------
\* The set of servers
CONSTANT Server
\* States of server
CONSTANTS LOOKING, FOLLOWING, LEADING
\* Zab states of server
CONSTANTS ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST
\* Message types
CONSTANTS CEPOCH, NEWEPOCH, ACKEPOCH, NEWLEADER, ACKLD, COMMITLD, PROPOSE, ACK, COMMIT
\* [MaxTimeoutFailures, MaxTransactionNum, MaxEpoch, MaxRestarts]
CONSTANT Parameters

Params1 == [MaxTimeoutFailures |-> 3, MaxTransactionNum |-> 5, MaxEpoch |-> 3, MaxRestarts |-> 2]

MAXEPOCH == 10
NullPoint == CHOOSE p: p \notin Server
Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}
-----------------------------------------------------------------------------
\* Variables that all servers use.
VARIABLES state,          \* State of server, in {LOOKING, FOLLOWING, LEADING}.
          zabState,       \* Current phase of server, in
                          \* {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}.
          acceptedEpoch,  \* Epoch of the last LEADERINFO packet accepted,
                          \* namely f.p in paper.
          currentEpoch,   \* Epoch of the last NEWLEADER packet accepted,
                          \* namely f.a in paper.
          history,        \* History of servers: sequence of transactions,
                          \* containing: [zxid, value, ackSid, epoch].
          lastCommitted   \* Maximum index and zxid known to be committed,
                          \* namely 'lastCommitted' in Leader. Starts from 0,
                          \* and increases monotonically before restarting.

\* Variables only used for leader.
VARIABLES learners,       \* Set of servers leader connects.
          cepochRecv,     \* Set of learners leader has received CEPOCH from.
                          \* Set of record [sid, connected, epoch],
                          \* where epoch means f.p from followers.
          ackeRecv,       \* Set of learners leader has received ACKEPOCH from.
                          \* Set of record 
                          \* [sid, connected, peerLastEpoch, peerHistory],
                          \* to record f.a and h(f) from followers.
          ackldRecv,      \* Set of learners leader has received ACKLD from.
                          \* Set of record [sid, connected].
          sendCounter     \* Count of txns leader has broadcast.

\* Variables only used for follower.
VARIABLES connectInfo \* If follower has connected with leader.
                      \* If follower lost connection, then null.

\* Variable representing oracle of leader.
VARIABLE  leaderOracle  \* Current oracle.

\* Variables about network channel.
\* Simulates network channel.
\* msgs[i][j] means the input buffer of server j 
\* from server i.
VARIABLE  msgs

\* Variables only used in verifying properties.
VARIABLES epochLeader,       \* Set of leaders in every epoch.
          proposalMsgsLog    \* Set of all broadcast messages.
        \*   violatedInvariants \* Check whether there are conditions 
                             \* contrary to the facts.

\* Variable used for recording critical data,
\* to constrain state space or update values.
\* VARIABLE  recorder \* Consists: members of Parameters and pc, values.
                   \* Form is record: 
                   \* [pc, nTransaction, maxEpoch, nTimeout, nRestart, nClientRequest]

serverVars == <<state, zabState, acceptedEpoch, currentEpoch, history, lastCommitted>>

leaderVars == <<learners, cepochRecv, ackeRecv, ackldRecv, 
                sendCounter>>

followerVars == connectInfo

electionVars == leaderOracle

msgVars == <<msgs>>

verifyVars == <<proposalMsgsLog, epochLeader>>

vars == <<serverVars, leaderVars, followerVars, electionVars, msgVars, verifyVars>>

\* Gives a candidate TypeOK definition for all variables in the spec.
TypeOK == 
    /\ state \in [Server -> {LOOKING, FOLLOWING, LEADING}]
    /\ zabState \in [Server -> {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}]
    /\ acceptedEpoch \in [Server -> Nat]
    /\ currentEpoch \in [Server -> Nat]
    /\ history \in [Server -> Seq([zxid: Nat, value: Nat, ackSid: Server, epoch: Nat])]
    /\ lastCommitted \in [Server -> [index: Nat, zxid: Nat \X Nat]]
    /\ learners \in [Server -> SUBSET Server]
    /\ cepochRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN, epoch: Nat]]
    /\ ackeRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: Seq([zxid: Nat, value: Nat, ackSid: Server, epoch: Nat])]]
    /\ ackldRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN]]
    /\ sendCounter \in [Server -> Nat]
    /\ connectInfo \in [Server -> Server]
    /\ leaderOracle \in Server
    /\ msgs = {}
    \* /\ msgs \in [Server -> [Server -> Seq([mtype: {CEPOCH, NEWEPOCH, ACKEPOCH, NEWLEADER, ACKLD, COMMITLD, PROPOSE, ACK, COMMIT}, 
                                            \* mepoch: Nat, 

CONSTANT MaxEpoch
CONSTANT MaxHistLen

Epoch == 1..MaxEpoch
Value == Nat

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

ZxidType == Epoch \X Nat

HistEntryType == [zxid: ZxidType, value: Nat, ackSid: SUBSET Server, epoch: Epoch]

HistTypeBounded == BoundedSeq(HistEntryType, MaxHistLen)

SetOfHistsTypeBounded == RandomSetOfSubsets(5, 5, HistTypeBounded)

AckeRecvTypeBounded == 
    RandomSetOfSubsets(1, 1, [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: HistTypeBounded]) \cup
    RandomSetOfSubsets(2, 2, [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: HistTypeBounded])

MsgCEPOCHType == [mtype: {CEPOCH}, mepoch: Epoch]
MsgNEWEPOCHType == [mtype: {NEWEPOCH}, mepoch: Epoch]
MsgACKEPOCHType == [mtype: {ACKEPOCH}, mepoch: Epoch, mhistory: HistTypeBounded]
MsgNEWLEADERType == [mtype: {NEWLEADER}, mepoch: Epoch, mhistory: HistTypeBounded]
MsgACKLDType == [mtype: {ACKLD}, mzxid: ZxidType]
MsgCOMMITLDType == [mtype: {COMMITLD}, mzxid: ZxidType]
MsgPROPOSEType == [mtype: {PROPOSE}, mzxid: ZxidType, mdata: Value]
MsgACKType == [mtype: {ACK}, mzxid: ZxidType]
MsgCOMMITType == [mtype: {COMMIT}, mzxid: ZxidType]

MsgType == 
    MsgCEPOCHType \cup 
    MsgNEWEPOCHType \cup 
    MsgACKEPOCHType \cup 
    MsgNEWLEADERType \cup 
    MsgACKLDType \cup 
    MsgCOMMITLDType \cup 
    MsgPROPOSEType \cup 
    MsgACKType \cup 
    MsgCOMMITType

MaxMsgChanLen == 1

CEpochRecvType == [sid: Server, connected: BOOLEAN, epoch: Epoch]

TypeOKRandom == 
    /\ state \in [Server -> {LOOKING, FOLLOWING, LEADING}]
    /\ zabState \in [Server -> {ELECTION, DISCOVERY, SYNCHRONIZATION, BROADCAST}]
    /\ acceptedEpoch \in [Server -> Epoch]
    /\ currentEpoch \in [Server -> Epoch]
    /\ history \in [Server -> HistTypeBounded]
    /\ lastCommitted \in [Server -> [index: Nat, zxid: ZxidType]]
    /\ learners \in [Server -> SUBSET Server]
    /\ cepochRecv \in [Server -> RandomSetOfSubsets(3, 3, CEpochRecvType)]
    /\ ackeRecv \in [Server -> AckeRecvTypeBounded]
    /\ ackldRecv \in [Server -> SUBSET [sid: Server, connected: BOOLEAN]]
    /\ sendCounter \in [Server -> Nat]
    /\ connectInfo \in [Server -> Server]
    /\ leaderOracle \in Server
    /\ msgs \in [Server -> [Server -> BoundedSeq(RandomSubset(7, MsgType), MaxMsgChanLen)]]
    /\ proposalMsgsLog    = {}
    /\ epochLeader        = [i \in 1..MaxEpoch |-> {} ]
    \* /\ violatedInvariants = {}
    \* /\ recorder = <<>>

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
ZxidCompare(zxid1, zxid2) == \/ zxid1[1] > zxid2[1]
                             \/ /\ zxid1[1] = zxid2[1]
                                /\ zxid1[2] > zxid2[2]

ZxidEqual(zxid1, zxid2) == zxid1[1] = zxid2[1] /\ zxid1[2] = zxid2[2]

TxnZxidEqual(txn, z) == txn.zxid[1] = z[1] /\ txn.zxid[2] = z[2]

TxnEqual(txn1, txn2) == /\ ZxidEqual(txn1.zxid, txn2.zxid)
                        /\ txn1.value = txn2.value

EpochPrecedeInTxn(txn1, txn2) == txn1.zxid[1] < txn2.zxid[1]
-----------------------------------------------------------------------------
\* Actions about recorder
GetParameter(p) == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE 0
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

CheckParameterHelper(n, p, Comp(_,_)) == IF p \in DOMAIN Parameters 
                                         THEN Comp(n, Parameters[p])
                                         ELSE TRUE
CheckParameterLimit(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

\* CheckTimeout        == CheckParameterLimit(recorder.nTimeout,     "MaxTimeoutFailures")
\* CheckTransactionNum == CheckParameterLimit(recorder.nTransaction, "MaxTransactionNum")
\* CheckEpoch          == CheckParameterLimit(recorder.maxEpoch,     "MaxEpoch")
\* CheckRestart        == /\ CheckTimeout 
\*                        /\ CheckParameterLimit(recorder.nRestart,  "MaxRestarts")

\* CheckStateConstraints == CheckTimeout /\ CheckTransactionNum /\ CheckEpoch /\ CheckRestart
-----------------------------------------------------------------------------
\* Actions about network
PendingCEPOCH(i, j)    == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = CEPOCH
PendingNEWEPOCH(i, j)  == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = NEWEPOCH
PendingACKEPOCH(i, j)  == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = ACKEPOCH
PendingNEWLEADER(i, j) == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = NEWLEADER
PendingACKLD(i, j)     == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = ACKLD
PendingCOMMITLD(i, j)  == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = COMMITLD
PendingPROPOSE(i, j)   == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = PROPOSE
PendingACK(i, j)       == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = ACK
PendingCOMMIT(i, j)    == /\ msgs[j][i] /= << >>
                          /\ msgs[j][i][1].mtype = COMMIT
\* Add a message to msgs - add a message m to msgs.
Send(i, j, m) == msgs' = [msgs EXCEPT ![i][j] = Append(msgs[i][j], m)]
SendIn(ms, i, j, m) == ms' = [ms EXCEPT ![i][j] = Append(ms[i][j], m)]
\* Remove a message from msgs - discard head of msgs.
Discard(i, j) == msgs' = IF msgs[i][j] /= << >> THEN [msgs EXCEPT ![i][j] = Tail(msgs[i][j])] ELSE msgs
DiscardIn(ms, i, j) == ms' = IF ms[i][j] /= << >> THEN [ms EXCEPT ![i][j] = Tail(ms[i][j])] ELSE ms
\* Combination of Send and Discard - discard head of msgs[j][i] and add m into msgs.
Reply(i, j, m) == msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m)]
ReplyIn(ms, i, j, m) == ms' = [ms EXCEPT ![j][i] = Tail(ms[j][i]),
                                       ![i][j] = Append(ms[i][j], m)]
\* Shuffle input buffer.
Clean(i, j) == 
    /\ msgs' = [msgs EXCEPT ![j][i] = << >>, ![i][j] = << >>]   

CleanInputBuffer(S) == 
    /\ msgs' = [s \in Server |-> [v \in Server |-> IF v \in S THEN << >> ELSE msgs[s][v] ] ]
\* Leader broadcasts a message PROPOSE to all other servers in Q.
\* Note: In paper, Q is fuzzy. We think servers who leader broadcasts NEWLEADER to
\*       should receive every PROPOSE. So we consider ackeRecv as Q.
\* Since we let ackeRecv = Q, there may exist some follower receiving COMMIT before
\* COMMITLD, and zxid in COMMIT later than zxid in COMMITLD. To avoid this situation,
\* if f \in ackeRecv but \notin ackldRecv, f should not receive COMMIT until 
\* f \in ackldRecv and receives COMMITLD.
Broadcast(i, m) ==
        LET ackeRecv_quorum == {a \in ackeRecv[i]: a.connected = TRUE }
            sid_ackeRecv == { a.sid: a \in ackeRecv_quorum }
        IN msgs' = [msgs EXCEPT ![i] = [v \in Server |-> IF /\ v \in sid_ackeRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]  
\* Since leader decides to broadcasts message COMMIT when processing ACK, so
\* we need to discard ACK and broadcast COMMIT.
\* Here Q is ackldRecv, because we assume that f should not receive COMMIT until
\* f receives COMMITLD.
DiscardAndBroadcast(i, j, m) ==
        LET ackldRecv_quorum == {a \in ackldRecv[i]: a.connected = TRUE }
            sid_ackldRecv == { a.sid: a \in ackldRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in sid_ackldRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]  
\* Leader broadcasts LEADERINFO to all other servers in cepochRecv.
DiscardAndBroadcastNEWEPOCH(i, j, m) ==
        LET new_cepochRecv_quorum == {c \in cepochRecv'[i]: c.connected = TRUE }
            new_sid_cepochRecv == { c.sid: c \in new_cepochRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in new_sid_cepochRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]
\* Leader broadcasts NEWLEADER to all other servers in ackeRecv.
DiscardAndBroadcastNEWLEADER(i, j, m) ==
        LET new_ackeRecv_quorum == {a \in ackeRecv'[i]: a.connected = TRUE }
            new_sid_ackeRecv == { a.sid: a \in new_ackeRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in new_sid_ackeRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]
\* Leader broadcasts COMMITLD to all other servers in ackldRecv.
DiscardAndBroadcastCOMMITLD(i, j, m) ==
        LET new_ackldRecv_quorum == {a \in ackldRecv'[i]: a.connected = TRUE }
            new_sid_ackldRecv == { a.sid: a \in new_ackldRecv_quorum }
        IN msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]),
                                ![i] = [v \in Server |-> IF /\ v \in new_sid_ackldRecv
                                                            /\ v \in learners[i] 
                                                            /\ v /= i
                                                         THEN Append(msgs[i][v], m)
                                                         ELSE msgs[i][v] ] ]
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
    /\ msgs = [s \in Server |-> [v \in Server |-> << >>] ]

InitVerifyVars == /\ proposalMsgsLog    = {}
                  /\ epochLeader        = [i \in 1..MAXEPOCH |-> {} ]
                \*   /\ violatedInvariants = {}
                \*   [stateInconsistent    |-> FALSE,
                \*                            proposalInconsistent |-> FALSE,
                \*                            commitInconsistent   |-> FALSE,
                \*                            ackInconsistent      |-> FALSE,
                \*                            messageIllegal       |-> FALSE ]

\* InitRecorder == recorder = <<>>
\* [nTimeout       |-> 0,
                            \* nTransaction   |-> 0,
                            \* maxEpoch       |-> 0,
                            \* nRestart       |-> 0,
                            \* pc             |-> <<"Init">>,
                            \* nClientRequest |-> 0]

Init == /\ InitServerVars
        /\ InitLeaderVars
        /\ InitFollowerVars
        /\ InitElectionVars
        /\ InitVerifyVars
        /\ InitMsgVars
        \* /\ InitRecorder
-----------------------------------------------------------------------------
\* Utils in state switching
FollowerShutdown(i) == 
        /\ state'    = [state      EXCEPT ![i] = LOOKING]
        /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
        /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]

LeaderShutdown(i) ==
        /\ LET S == learners[i]
           IN /\ state' = [s \in Server |-> IF s \in S THEN LOOKING ELSE state[s] ]
              /\ zabState' = [s \in Server |-> IF s \in S THEN ELECTION ELSE zabState[s] ]
              /\ connectInfo' = [s \in Server |-> IF s \in S THEN NullPoint ELSE connectInfo[s] ]
              /\ CleanInputBuffer(S)
        /\ learners'   = [learners   EXCEPT ![i] = {}]

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

RemoveCepochRecv(set, sid) ==
        LET sid_cepochRecv == {s.sid: s \in set}
        IN IF sid \notin sid_cepochRecv THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid       |-> sid,
                                  connected |-> FALSE,
                                  epoch     |-> info.epoch ]
                IN (set \ {info}) \union {new_info}

RemoveAckeRecv(set, sid) ==
        LET sid_ackeRecv == {s.sid: s \in set}
        IN IF sid \notin sid_ackeRecv THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid |-> sid,
                                  connected |-> FALSE,
                                  peerLastEpoch |-> info.peerLastEpoch,
                                  peerHistory   |-> info.peerHistory ]
                IN (set \ {info}) \union {new_info}

RemoveAckldRecv(set, sid) ==
        LET sid_ackldRecv == {s.sid: s \in set}
        IN IF sid \notin sid_ackldRecv THEN set
           ELSE LET info == CHOOSE s \in set: s.sid = sid
                    new_info == [ sid |-> sid,
                                  connected |-> FALSE ]
                IN (set \ {info}) \union {new_info}

RemoveLearner(i, j) ==
        /\ learners'   = [learners   EXCEPT ![i] = @ \ {j}] 
        /\ cepochRecv' = [cepochRecv EXCEPT ![i] = RemoveCepochRecv(@, j) ]
        /\ ackeRecv'   = [ackeRecv   EXCEPT ![i] = RemoveAckeRecv(@, j) ]
        /\ ackldRecv'  = [ackldRecv  EXCEPT ![i] = RemoveAckldRecv(@, j) ]
-----------------------------------------------------------------------------
\* Actions of election
UpdateLeader(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= i
        /\ leaderOracle' = i
        /\ SwitchToLeader(i)
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, followerVars, verifyVars, msgVars>>
        /\ UpdateRecorder(<<"UpdateLeader", i>>)


FollowLeaderMyself(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= NullPoint
        /\ leaderOracle = i
        /\ SwitchToLeader(i)
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, electionVars, followerVars, verifyVars, msgVars>>

FollowLeaderOther(i) ==
        /\ IsLooking(i)
        /\ leaderOracle /= NullPoint
        /\ leaderOracle /= i
        /\ SwitchToFollower(i)
        /\ UNCHANGED <<leaderVars, acceptedEpoch, currentEpoch, history, lastCommitted, electionVars, followerVars, verifyVars, msgVars>>

-----------------------------------------------------------------------------
(* Actions of situation error. Situation error in protocol spec is different
   from latter specs. This is for compressing state space, we focus on results
   from external events (e.g. network partition, node failure, etc.), so we do
   not need to add variables and actions about network conditions and node 
   conditions. It is reasonable that we have action 'Restart' but no 'Crash',
   because when a node does not execute any internal events after restarting, 
   this is equivalent to executing a crash.
*)

\* Timeout between leader and follower.  
TimeoutWithQuorum(i, j) ==
        \* /\ CheckTimeout \* test restrictions of timeout
        /\ IsLeader(i)   
        /\ IsMyLearner(i, j)
        /\ IsFollower(j) 
        /\ IsMyLeader(j, i)
        /\ (learners[i] \ {j}) \in Quorums  \* just remove this learner
        /\ RemoveLearner(i, j)
        /\ FollowerShutdown(j)
        /\ Clean(i, j)
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, lastCommitted, sendCounter, electionVars, verifyVars>>

TimeoutNoQuorum(i, j) ==
        \* /\ CheckTimeout \* test restrictions of timeout
        /\ IsLeader(i)   
        /\ IsMyLearner(i, j)
        /\ IsFollower(j) 
        /\ IsMyLeader(j, i)
        /\ (learners[i] \ {j}) \notin Quorums \* leader switches to looking
        /\ state' = [s \in Server |-> IF s \in learners[i] THEN LOOKING ELSE state[s] ]
        /\ zabState' = [s \in Server |-> IF s \in learners[i] THEN ELECTION ELSE zabState[s] ]
        /\ connectInfo' = [s \in Server |-> IF s \in learners[i] THEN NullPoint ELSE connectInfo[s] ]
        /\ CleanInputBuffer(learners[i])
        /\ learners'   = [learners   EXCEPT ![i] = {}]
        /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv, acceptedEpoch, currentEpoch, history, lastCommitted, sendCounter, electionVars, verifyVars>>

Restart(i) ==
        \* /\ CheckRestart \* test restrictions of restart
        /\ \/ /\ IsLooking(i)
              /\ UNCHANGED <<state, zabState, learners, followerVars, msgVars,
                    cepochRecv, ackeRecv, ackldRecv>>
           \/ /\ IsFollower(i)
              /\ LET connectedWithLeader == HasLeader(i)
                 IN \/ /\ connectedWithLeader
                       /\ LET leader == connectInfo[i]
                              newLearners == learners[leader] \ {i}
                          IN 
                          \/ /\ IsQuorum(newLearners)  \* leader remove learner i
                             /\ RemoveLearner(leader, i)
                             /\ FollowerShutdown(i)
                             /\ Clean(leader, i)
                          \/ /\ ~IsQuorum(newLearners) \* leader switches to looking
                             /\ LeaderShutdown(leader)
                             /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
                    \/ /\ ~connectedWithLeader
                       /\ FollowerShutdown(i)
                       /\ CleanInputBuffer({i})
                       /\ UNCHANGED <<learners, cepochRecv, ackeRecv, ackldRecv>>
           \/ /\ IsLeader(i)
              /\ LeaderShutdown(i)
              /\ UNCHANGED <<cepochRecv, ackeRecv, ackldRecv>>
        /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> 0,
                                                           zxid  |-> <<0, 0>> ] ]
        /\ UNCHANGED <<acceptedEpoch, currentEpoch, history, sendCounter, leaderOracle, verifyVars>>
        /\ UpdateRecorder(<<"Restart", i>>)
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
    /\ Send(j, i, [ mtype  |-> CEPOCH, mepoch |-> acceptedEpoch[j] ]) \* contains f.p
    /\ UNCHANGED <<serverVars, electionVars, verifyVars, cepochRecv, ackeRecv, ackldRecv, sendCounter>>

CepochRecvQuorumFormed(i) == LET sid_cepochRecv == {c.sid: c \in cepochRecv[i]} IN IsQuorum(sid_cepochRecv)
CepochRecvBecomeQuorum(i) == LET sid_cepochRecv == {c.sid: c \in cepochRecv'[i]} IN IsQuorum(sid_cepochRecv)

UpdateCepochRecv(oldSet, sid, peerEpoch) ==
        LET sid_set == {s.sid: s \in oldSet}
        IN IF sid \in sid_set
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
LeaderProcessCEPOCH(i, j) ==
        \* /\ CheckEpoch  \* test restrictions of max epoch
        /\ IsLeader(i)
        /\ PendingCEPOCH(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
           IN /\ infoOk
              /\ \/ \* 1. has not broadcast NEWEPOCH
                    /\ ~CepochRecvQuorumFormed(i)
                    /\ zabState[i] = DISCOVERY
                    \* /\ UNCHANGED violatedInvariants
                    /\ cepochRecv' = [cepochRecv EXCEPT ![i] = UpdateCepochRecv(@, j, msg.mepoch) ]
                    /\ \/ \* 1.1. cepochRecv becomes quorum, 
                          \* then determine e' and broadcasts NEWEPOCH in Q. 
                          /\ CepochRecvBecomeQuorum(i)
                          /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = DetermineNewEpoch(i)]
                          /\ LET m == [ mtype  |-> NEWEPOCH,
                                        mepoch |-> acceptedEpoch'[i] ]
                             IN DiscardAndBroadcastNEWEPOCH(i, j, m)
                       \/ \* 1.2. cepochRecv still not quorum.
                          /\ ~CepochRecvBecomeQuorum(i)
                          /\ DiscardIn(msgs ,j, i)
                          /\ UNCHANGED acceptedEpoch
                 \/ \* 2. has broadcast NEWEPOCH
                    /\ CepochRecvQuorumFormed(i)
                    /\ cepochRecv' = [cepochRecv EXCEPT ![i] = UpdateCepochRecv(@, j, msg.mepoch) ]
                    /\ msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), 
                                            ![i][j] = Append(msgs[i][j], 
                                                [ mtype  |-> NEWEPOCH,
                                                  mepoch |-> acceptedEpoch[i] ])]
                    /\ UNCHANGED <<acceptedEpoch>>
        /\ UNCHANGED <<state, zabState, currentEpoch, history, lastCommitted, learners, 
                       ackeRecv, ackldRecv, sendCounter, followerVars,
                       electionVars, proposalMsgsLog, epochLeader>>
        /\ UpdateRecorder(<<"LeaderProcessCEPOCH", i, j>>)

(* Follower receives LEADERINFO. If newEpoch >= acceptedEpoch, then follower 
   updates acceptedEpoch and sends ACKEPOCH back, containing currentEpoch and
   history. After this, zabState turns to SYNC. *)
FollowerProcessNEWEPOCH(i, j) ==
        /\ IsFollower(i)
        /\ PendingNEWEPOCH(i, j)
        /\ LET msg     == msgs[j][i][1]
               infoOk  == IsMyLeader(i, j)
               stateOk == zabState[i] = DISCOVERY
               epochOk == msg.mepoch >= acceptedEpoch[i]
           IN /\ infoOk
              /\ \/ \* 1. Normal case
                    /\ epochOk
                    /\ \/ /\ stateOk
                          /\ acceptedEpoch' = [acceptedEpoch EXCEPT ![i] = msg.mepoch]
                          /\ LET m == [ mtype    |-> ACKEPOCH,
                                        mepoch   |-> currentEpoch[i],
                                        mhistory |-> history[i] ]
                             IN Reply(i, j, m)
                          /\ zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]
                        \*   /\ UNCHANGED violatedInvariants
                    /\ UNCHANGED <<followerVars, learners, cepochRecv, ackeRecv, ackldRecv, state>>
                 \/ \* 2. Abnormal case - go back to election
                    /\ ~epochOk
                    /\ FollowerShutdown(i)
                    /\ LET leader == connectInfo[i]
                       IN /\ Clean(i, leader)
                          /\ RemoveLearner(leader, i)
                    /\ UNCHANGED <<acceptedEpoch>>
        /\ UNCHANGED <<currentEpoch, history, lastCommitted, sendCounter, electionVars, proposalMsgsLog, epochLeader>>
        /\ UpdateRecorder(<<"FollowerProcessNEWEPOCH", i, j>>)

AckeRecvQuorumFormed(i) == LET sid_ackeRecv == {a.sid: a \in ackeRecv[i]} IN IsQuorum(sid_ackeRecv)
AckeRecvBecomeQuorum(i) == LET sid_ackeRecv == {a.sid: a \in ackeRecv'[i]} IN IsQuorum(sid_ackeRecv)

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
RECURSIVE SetPacketsForChecking(_,_,_,_,_,_)
SetPacketsForChecking(set, src, ep, his, cur, end) ==
        IF cur > end THEN set
        ELSE LET m_proposal == [ source |-> src,
                                 epoch  |-> ep,
                                 zxid   |-> his[cur].zxid,
                                 data   |-> his[cur].value ]
             IN SetPacketsForChecking((set \union {m_proposal}), src, ep, his, cur + 1, end)
    

LastZxidOfHistory(his) == IF Len(his) = 0 THEN <<0, 0>>
                          ELSE his[Len(his)].zxid

\* TRUE: f1.a > f2.a or (f1.a = fa.a and f1.zxid >= f2.zxid)
MoreRecentOrEqual(ss1, ss2) == \/ ss1.currentEpoch > ss2.currentEpoch
                               \/ /\ ss1.currentEpoch = ss2.currentEpoch
                                  /\ ~ZxidCompare(ss2.lastZxid, ss1.lastZxid)

DetermineInitialHistoryFromArg(ackeRecvArg, i) ==
        LET set == ackeRecvArg[i]
            ss_set == { [ sid          |-> a.sid,
                          currentEpoch |-> a.peerLastEpoch,
                          lastZxid     |-> LastZxidOfHistory(a.peerHistory) ] : a \in ackeRecvArg[i] }
            \* Choose server with most recent history.
            selected == CHOOSE ss \in ss_set: \A ss1 \in (ss_set \ {ss}): MoreRecentOrEqual(ss, ss1)
            info == CHOOSE f \in ackeRecvArg[i] : f.sid = selected.sid
        IN info.peerHistory

\* Determine initial history Ie' in this round from a quorum of ACKEPOCH.
DetermineInitialHistory(i) ==
        LET set == ackeRecv'[i]
            ss_set == { [ sid          |-> a.sid,
                          currentEpoch |-> a.peerLastEpoch,
                          lastZxid     |-> LastZxidOfHistory(a.peerHistory) ]
                        : a \in set }
            selected == CHOOSE ss \in ss_set: 
                            \A ss1 \in (ss_set \ {ss}): MoreRecentOrEqual(ss, ss1)
            info == CHOOSE f \in set: f.sid = selected.sid
        IN info.peerHistory

RECURSIVE InitAcksidHelper(_,_)
InitAcksidHelper(txns, src) == IF Len(txns) = 0 THEN << >>
                               ELSE LET oldTxn == txns[1]
                                        newTxn == [ zxid   |-> oldTxn.zxid,
                                                    value  |-> oldTxn.value,
                                                    ackSid |-> {src},
                                                    epoch  |-> oldTxn.epoch ]
                                    IN <<newTxn>> \o InitAcksidHelper( Tail(txns), src)

\* Atomically let all txns in initial history contain self's acks.
InitAcksid(i, his) == InitAcksidHelper(his, i)

(* Leader waits for receiving ACKEPOPCH from a quorum, and determines initialHistory
   according to history of whom has most recent state summary from them. After this,
   leader's zabState turns to SYNCHRONIZATION. *)
\* Has broadcast NEWLEADER.
LeaderProcessACKEPOCHHasBroadcast(i, j) ==
        /\ IsLeader(i)
        /\ PendingACKEPOCH(i, j)
        /\ IsMyLearner(i, j)
        /\ LET msg == msgs[j][i][1]
           IN \* 1. has broadcast NEWLEADER 
              /\ IsQuorum({a.sid: a \in ackeRecv[i]})
              /\ ackeRecv' = [ackeRecv EXCEPT ![i] = UpdateAckeRecv(ackeRecv[i], j,msg.mepoch, msg.mhistory) ]
              /\ LET toSend == history[i] \* contains (Ie', Be')
                     m == [ mtype    |-> NEWLEADER,
                            mepoch   |-> acceptedEpoch[i],
                            mhistory |-> toSend ] IN 
                            msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m)]
                    \* Ignore 'proposalMsgs' updates for now and safety properties that depend on it.
                    \*  set_forChecking == SetPacketsForChecking({ }, i, acceptedEpoch[i], toSend, 1, Len(toSend)) IN 
                    \*  /\ Reply(i, j, m) 
                    \*  /\ proposalMsgsLog' = proposalMsgsLog \*\union set_forChecking
              /\ UNCHANGED <<proposalMsgsLog, currentEpoch, history, zabState, epochLeader, state, acceptedEpoch, lastCommitted, learners, cepochRecv, ackldRecv, sendCounter, followerVars, electionVars>>

(* Leader waits for receiving ACKEPOPCH from a quorum, and determines initialHistory
   according to history of whom has most recent state summary from them. After this,
   leader's zabState turns to SYNCHRONIZATION. *)
\* Has not broadcast NEWLEADER yet.
LeaderProcessACKEPOCHHasntBroadcast(i, j) ==
    /\ IsLeader(i)
    /\ PendingACKEPOCH(i, j)
    /\ LET msg == msgs[j][i][1]
            infoOk == IsMyLearner(i, j)
        IN  /\ infoOk
            \* 2. has not broadcast NEWLEADER
            /\ ~AckeRecvQuorumFormed(i)
            /\ zabState[i] = DISCOVERY
            /\ ackeRecv' = [ackeRecv EXCEPT ![i] = UpdateAckeRecv(@, j,msg.mepoch, msg.mhistory) ]
                \* 2.1. ackeRecv becomes quorum, determine Ie'
                \* and broacasts NEWLEADER in Q. (l.1.2 + l.2.1)
            /\  \/ /\ AckeRecvBecomeQuorum(i)
                   /\ \* Update f.a
                      LET newLeaderEpoch == acceptedEpoch[i] IN 
                      /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newLeaderEpoch]
                      /\ epochLeader' = [epochLeader EXCEPT ![newLeaderEpoch] = @ \union {i} ] \* for checking invariants
                      /\ \* Determine initial history Ie'
                            LET initialHistory == DetermineInitialHistory(i) IN 
                            history' = [history EXCEPT ![i] = InitAcksid(i, initialHistory) ]
                      /\ zabState' = [zabState EXCEPT ![i] = SYNCHRONIZATION]
                      /\ \* Broadcast NEWLEADER with (e', Ie')
                            LET toSend == history'[i] 
                                m == [  mtype    |-> NEWLEADER,
                                        mepoch   |-> acceptedEpoch[i],
                                        mhistory |-> toSend ] IN DiscardAndBroadcastNEWLEADER(i, j, m)
                \/  \* 2.2. ackeRecv still not quorum.
                    /\ ~AckeRecvBecomeQuorum(i)
                    /\ Discard(j, i)
                    /\ UNCHANGED <<currentEpoch, history, zabState, proposalMsgsLog, epochLeader>>
    /\ UNCHANGED <<proposalMsgsLog,state, acceptedEpoch, lastCommitted, learners, cepochRecv, ackldRecv, sendCounter, followerVars, electionVars>>

-----------------------------------------------------------------------------    
(* Follower receives NEWLEADER. Update f.a and history. *)
FollowerProcessNEWLEADER(i, j) ==
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ LET msg == msgs[j][i][1] IN
              \* 2. f.p equals e'.
              /\ IsMyLeader(i, j)
              /\ acceptedEpoch[i] = msg.mepoch
              /\ zabState[i] = SYNCHRONIZATION
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = acceptedEpoch[i]]
              /\ history' = [history EXCEPT ![i] = msg.mhistory] \* no need to care ackSid
              /\ LET m == [ mtype |-> ACKLD, mzxid |-> LastZxidOfHistory(history'[i]) ] IN
                        msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m)]
              /\ UNCHANGED <<followerVars, state, zabState, learners, cepochRecv, ackeRecv, ackldRecv, acceptedEpoch, lastCommitted, sendCounter, electionVars, proposalMsgsLog, epochLeader>>

FollowerProcessNEWLEADERNewIteration(i, j) ==
        /\ IsFollower(i)
        /\ PendingNEWLEADER(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               epochOk == acceptedEpoch[i] = msg.mepoch
               stateOk == zabState[i] = SYNCHRONIZATION
           IN /\ infoOk
              \* 1. f.p not equals e', starts a new iteration.
              /\ ~epochOk
              /\ state'    = [state      EXCEPT ![i] = LOOKING]
              /\ zabState' = [zabState   EXCEPT ![i] = ELECTION]
              /\ connectInfo' = [connectInfo EXCEPT ![i] = NullPoint]
              /\ LET leader == connectInfo[i]
                  IN /\ Clean(i, leader)
                     /\ RemoveLearner(leader, i)
              /\ UNCHANGED <<currentEpoch, history, acceptedEpoch, lastCommitted, sendCounter, electionVars, proposalMsgsLog, epochLeader>>

AckldRecvQuorumFormed(i) == LET sid_ackldRecv == {a.sid: a \in ackldRecv[i]} IN IsQuorum(sid_ackldRecv)
AckldRecvBecomeQuorum(i) == LET sid_ackldRecv == {a.sid: a \in ackldRecv'[i]} IN IsQuorum(sid_ackldRecv)

UpdateAckldRecv(oldSet, sid) ==
        LET sid_set == {s.sid: s \in oldSet}
            follower_info == [ sid       |-> sid,
                               connected |-> TRUE ]
        IN IF sid \in sid_set
           THEN LET old_info == CHOOSE info \in oldSet: info.sid = sid
                IN (oldSet \ {old_info}) \union {follower_info}
           ELSE oldSet \union {follower_info}

LastZxid(i) == LastZxidOfHistory(history[i])

RECURSIVE UpdateAcksidHelper(_,_,_)
UpdateAcksidHelper(txns, target, endZxid) ==
        IF Len(txns) = 0 THEN << >>
        ELSE LET oldTxn == txns[1]
             IN IF ZxidCompare(oldTxn.zxid, endZxid) THEN txns
                ELSE LET newTxn == [ zxid   |-> oldTxn.zxid,
                                     value  |-> oldTxn.value,
                                     ackSid |-> IF target \in oldTxn.ackSid
                                                THEN oldTxn.ackSid
                                                ELSE oldTxn.ackSid \union {target},
                                     epoch  |-> oldTxn.epoch ]
                     IN <<newTxn>> \o UpdateAcksidHelper( Tail(txns), target, endZxid)
    
\* Atomically add ackSid of one learner according to zxid in ACKLD.
UpdateAcksid(his, target, endZxid) == UpdateAcksidHelper(his, target, endZxid)

UpdateAcksidExpr(his, target, endZxid) == 
    LET zxidIndicesLessThanEnd == {i \in DOMAIN his : ~ZxidCompare(his[i].zxid, endZxid)}
        firstZxidIndex == IF zxidIndicesLessThanEnd # {} 
                            THEN Maximum(zxidIndicesLessThanEnd)
                            ELSE 100 IN
    [idx \in DOMAIN his |-> 
        IF firstZxidIndex >= 0 /\ idx <= firstZxidIndex 
            THEN [his[idx] EXCEPT !.ackSid = his[idx].ackSid \cup {target}]
            ELSE his[idx]
    ]

\* TODO: Get this working properly.
UpdateAcksAreEquiv == \A s,t \in Server : \A zxid \in (1..MaxEpoch) \X (1..MaxEpoch) : 
    /\ PrintT(zxid)
    /\ PrintT(t)
    /\ PrintT(UpdateAcksid(history[s], t, zxid))
    /\ PrintT(UpdateAcksidExpr(history[s], t, zxid))
    /\ UpdateAcksid(history[s], t, zxid) = UpdateAcksidExpr(history[s], t, zxid) 

(* Leader waits for receiving ACKLD from a quorum including itself,
   and broadcasts COMMITLD and turns to BROADCAST. *)
LeaderProcessACKLDHasntBroadcast(i, j) ==
        /\ IsLeader(i)
        /\ PendingACKLD(i, j)
        /\ LET msg == msgs[j][i][1] IN
              /\ IsMyLearner(i, j)
              \* 1. has not broadcast COMMITLD
              /\ ~AckldRecvQuorumFormed(i)
              /\ zabState[i] = SYNCHRONIZATION 
              /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(ackldRecv[i], j) ]
              /\ history' = [history EXCEPT ![i] = UpdateAcksid(history[i], j, msg.mzxid)]
                    \* 1.1. ackldRecv becomes quorum,
                    \* then broadcasts COMMITLD and turns to BROADCAST.
              /\ \/ /\ AckldRecvBecomeQuorum(i)
                    /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> Len(history[i]), zxid  |-> LastZxid(i) ] ]
                    /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
                    /\ LET m == [ mtype |-> COMMITLD, mzxid |-> LastZxid(i) ] IN DiscardAndBroadcastCOMMITLD(i, j, m)
                 \/ \* 1.2. ackldRecv still not quorum.
                    /\ ~AckldRecvBecomeQuorum(i)
                    /\ Discard(j, i)
                    /\ UNCHANGED <<zabState, lastCommitted>>
        /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, sendCounter, followerVars, electionVars, proposalMsgsLog, epochLeader>>

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
\*         /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, sendCounter, followerVars, electionVars, proposalMsgsLog, epochLeader>>


(* Leader waits for receiving ACKLD from a quorum including itself,
   and broadcasts COMMITLD and turns to BROADCAST. *)
LeaderProcessACKLDHasBroadcast(i, j) ==
        /\ IsLeader(i)
        /\ PendingACKLD(i, j)
        /\ AckldRecvQuorumFormed(i)
        /\ IsMyLearner(i, j)
        /\ LET msg == msgs[j][i][1] IN
              \* 2. has broadcast COMMITLD
              /\ zabState[i] = BROADCAST 
              /\ ackldRecv' = [ackldRecv EXCEPT ![i] = UpdateAckldRecv(@, j) ]
              /\ history' = [history EXCEPT ![i] = UpdateAcksid(@, j, msg.mzxid)]
            \*   /\ history' = [history EXCEPT ![i] = UpdateAcksidExpr(@, j, msg.mzxid)] \* TODO: Eventually switch to this.
              /\ msgs' = [msgs EXCEPT 
                            ![j][i] = Tail(msgs[j][i]), 
                            ![i][j] = Append(msgs[i][j], [ mtype |-> COMMITLD, mzxid |-> lastCommitted[i].zxid ])]
        /\ UNCHANGED <<zabState, lastCommitted, state, acceptedEpoch, currentEpoch, learners, cepochRecv, ackeRecv, sendCounter, followerVars, electionVars, proposalMsgsLog, epochLeader>>

RECURSIVE ZxidToIndexHepler(_,_,_,_)
ZxidToIndexHepler(his, zxid, cur, appeared) == 
        IF cur > Len(his) THEN cur  
        ELSE IF TxnZxidEqual(his[cur], zxid) 
             THEN (IF appeared = TRUE 
                    THEN -1 
                    ELSE Minimum( { cur, ZxidToIndexHepler(his, zxid, cur + 1, TRUE) } ))
             ELSE ZxidToIndexHepler(his, zxid, cur + 1, appeared)

\* return -1: this zxid appears at least twice. 
\* Len(his) + 1: does not exist.
\* 1 - Len(his): exists and appears just once.
ZxidToIndex(his, zxid) == 
    IF ZxidEqual( zxid, <<0, 0>> ) THEN 0
        ELSE 
            IF Len(his) = 0 THEN 1
            ELSE LET len == Len(his) IN
                IF \E idx \in 1..len: TxnZxidEqual(his[idx], zxid)
                    THEN ZxidToIndexHepler(his, zxid, 1, FALSE)
                    ELSE len + 1

(* Follower receives COMMITLD. Commit all txns. *)
FollowerProcessCOMMITLD(i, j) ==
        /\ IsFollower(i)
        /\ PendingCOMMITLD(i, j)
        /\ IsMyLeader(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               index == IF ZxidEqual(msg.mzxid, <<0, 0>>) 
                            THEN 0
                            ELSE ZxidToIndex(history[i], msg.mzxid)
               logOk == index >= 0 /\ index <= Len(history[i])
           IN /\ infoOk
              /\ logOk
              /\ lastCommitted' = [lastCommitted EXCEPT ![i] = [ index |-> index,
                                                                 zxid  |-> msg.mzxid ] ]
              /\ zabState' = [zabState EXCEPT ![i] = BROADCAST]
              \* Discard the message. (Will S. 10/26/23)
              /\ msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i])]
              /\ UNCHANGED <<state, acceptedEpoch, currentEpoch, history, leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>
----------------------------------------------------------------------------
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
            /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, lastCommitted,
                        leaderVars, followerVars, electionVars, msgVars, verifyVars>>
            /\ UpdateRecorder(<<"LeaderProcessRequest", i>>)

\* Latest counter existing in history.
CurrentCounter(i) == IF LastZxid(i)[1] = currentEpoch[i] THEN LastZxid(i)[2]
                     ELSE 0

(* Leader broadcasts PROPOSE when sendCounter < currentCounter. *)
LeaderBroadcastPROPOSE(i) == 
        /\ IsLeader(i)
        /\ zabState[i] = BROADCAST
        /\ sendCounter[i] < CurrentCounter(i) \* there exists proposal to be sent
         \* Explicit check here to avoid out-of-bounds access. (Will S. 10/26/23)
        /\ ZxidToIndex(history[i], <<currentEpoch[i], sendCounter[i] + 1>>) \in DOMAIN history[i]
        /\ LET toSendCounter == sendCounter[i] + 1
               toSendZxid == <<currentEpoch[i], toSendCounter>>
               toSendIndex == ZxidToIndex(history[i], toSendZxid)
               toSendTxn == history[i][toSendIndex]
               m_proposal == [ mtype |-> PROPOSE,
                               mzxid |-> toSendTxn.zxid,
                               mdata |-> toSendTxn.value ]
               m_proposal_forChecking == [ source |-> i,
                                           epoch  |-> currentEpoch[i],
                                           zxid   |-> toSendTxn.zxid,
                                           data   |-> toSendTxn.value ]
           IN /\ sendCounter' = [sendCounter EXCEPT ![i] = toSendCounter]
              /\ Broadcast(i, m_proposal)
              /\ proposalMsgsLog' = proposalMsgsLog \union {m_proposal_forChecking}
        /\ UNCHANGED <<serverVars, learners, cepochRecv, ackeRecv, ackldRecv, 
                followerVars, electionVars, epochLeader>>
        /\ UpdateRecorder(<<"LeaderBroadcastPROPOSE", i>>)

IsNextZxid(curZxid, nextZxid) ==
            \/ \* first PROPOSAL in this epoch
               /\ nextZxid[2] = 1
               /\ curZxid[1] < nextZxid[1]
            \/ \* not first PROPOSAL in this epoch
               /\ nextZxid[2] > 1
               /\ curZxid[1] = nextZxid[1]
               /\ curZxid[2] + 1 = nextZxid[2]

(* Follower processes PROPOSE, saves it in history and replies ACK. *)
FollowerProcessPROPOSE(i, j) ==
        /\ IsFollower(i)
        /\ PendingPROPOSE(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               isNext == IsNextZxid(LastZxid(i), msg.mzxid)
               newTxn == [ zxid   |-> msg.mzxid,
                           value  |-> msg.mdata,
                           ackSid |-> {},
                           epoch  |-> currentEpoch[i] ]
               m_ack == [ mtype |-> ACK,
                          mzxid |-> msg.mzxid ]
           IN /\ infoOk
              /\ \/ /\ isNext
                    /\ history' = [history EXCEPT ![i] = Append(@, newTxn)]
                    /\ msgs' = [msgs EXCEPT ![j][i] = Tail(msgs[j][i]), ![i][j] = Append(msgs[i][j], m_ack)]
                 \/ /\ ~isNext
                    /\ LET index == ZxidToIndex(history[i], msg.mzxid)
                           exist == index > 0 /\ index <= Len(history[i]) IN exist
                    /\ Discard(j, i)
                    /\ UNCHANGED history
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, lastCommitted, leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>

LeaderTryToCommit(s, index, zxid, newTxn, follower) ==
        LET allTxnsBeforeCommitted == lastCommitted[s].index >= index - 1
                    \* Only when all proposals before zxid has been committed,
                    \* this proposal can be permitted to be committed.
            hasAllQuorums == IsQuorum(newTxn.ackSid)
                    \* In order to be committed, a proposal must be accepted
                    \* by a quorum.
            ordered == lastCommitted[s].index + 1 = index
                    \* Commit proposals in order.
        IN \/ /\ \* Current conditions do not satisfy committing the proposal.
                 \/ ~allTxnsBeforeCommitted
                 \/ ~hasAllQuorums
              /\ Discard(follower, s)
              /\ UNCHANGED <<lastCommitted>>
           \/ /\ allTxnsBeforeCommitted
              /\ hasAllQuorums
              /\ \/ /\ ordered
              /\ lastCommitted' = [lastCommitted EXCEPT ![s] = [ index |-> index,
                                                                 zxid  |-> zxid ] ]
              /\ LET m_commit == [ mtype |-> COMMIT,
                                   mzxid |-> zxid ]
                 IN DiscardAndBroadcast(s, follower, m_commit)


LastAckIndexFromFollower(i, j) == 
        LET set_index == {idx \in 1..Len(history[i]): j \in history[i][idx].ackSid }
        IN Maximum(set_index)


(* Leader Keeps a count of acks for a particular proposal, and try to
   commit the proposal. If committed, COMMIT of proposal will be broadcast. *)
LeaderProcessACKAlreadyCommitted(i, j) ==
        /\ IsLeader(i)
        /\ PendingACK(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
               index == ZxidToIndex(history[i], msg.mzxid)
               exist == index >= 1 /\ index <= Len(history[i]) \* proposal exists in history
               outstanding == lastCommitted[i].index < Len(history[i]) \* outstanding not null
               hasCommitted == ~ZxidCompare(msg.mzxid, lastCommitted[i].zxid)
               ackIndex == LastAckIndexFromFollower(i, j)
               monotonicallyInc == \/ ackIndex = -1
                                   \/ ackIndex + 1 = index
           IN /\ infoOk
              /\ exist
              /\ monotonicallyInc
              /\ LET txn == history[i][index]
                     txnAfterAddAck == [ zxid   |-> txn.zxid,
                                               value  |-> txn.value,
                                               ackSid |-> txn.ackSid \union {j} ,
                                               epoch  |-> txn.epoch ] IN
                       /\ history' = [history EXCEPT ![i][index] = txnAfterAddAck ]
                       /\ \* Note: outstanding is 0. 
                            \* / proposal has already been committed.
                            \/ ~outstanding
                            \/ hasCommitted
                       /\ Discard(j, i)
                       /\ UNCHANGED <<lastCommitted>>
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>
        /\ UpdateRecorder(<<"LeaderProcessACK", i, j>>)

(* Leader Keeps a count of acks for a particular proposal, and try to
   commit the proposal. If committed, COMMIT of proposal will be broadcast. *)
LeaderProcessACK(i, j) ==
        /\ IsLeader(i)
        /\ PendingACK(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLearner(i, j)
               index == ZxidToIndex(history[i], msg.mzxid)
               exist == index >= 1 /\ index <= Len(history[i]) \* proposal exists in history
               outstanding == lastCommitted[i].index < Len(history[i]) \* outstanding not null
               hasCommitted == ~ZxidCompare(msg.mzxid, lastCommitted[i].zxid)
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
                          /\ LeaderTryToCommit(i, index, msg.mzxid, txnAfterAddAck, j)
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>

(* Follower processes COMMIT. *)
FollowerProcessCOMMIT(i, j) ==
        /\ IsFollower(i)
        /\ PendingCOMMIT(i, j)
        /\ LET msg == msgs[j][i][1]
               infoOk == IsMyLeader(i, j)
               pending == lastCommitted[i].index < Len(history[i])
           IN /\ infoOk
              /\ pending
              /\ LET firstElement == history[i][lastCommitted[i].index + 1]
                           match == ZxidEqual(firstElement.zxid, msg.mzxid) IN
                    /\ match
                    /\ lastCommitted' = [lastCommitted EXCEPT ![i] = 
                                            [   index |-> lastCommitted[i].index + 1,
                                                zxid  |-> firstElement.zxid ] ]
        /\ Discard(j, i)
        /\ UNCHANGED <<state, zabState, acceptedEpoch, currentEpoch, history,leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>
----------------------------------------------------------------------------     
(* Used to discard some messages which should not exist in network channel.
   This action should not be triggered. *)
FilterNonexistentMessage(i) ==
        /\ \E j \in Server \ {i}: /\ msgs[j][i] /= << >>
                                  /\ LET msg == msgs[j][i][1]
                                     IN 
                                        \/ /\ IsLeader(i)
                                           /\ LET infoOk == IsMyLearner(i, j)
                                              IN
                                              \/ msg.mtype = NEWEPOCH
                                              \/ msg.mtype = NEWLEADER
                                              \/ msg.mtype = COMMITLD
                                              \/ msg.mtype = PROPOSE
                                              \/ msg.mtype = COMMIT
                                              \/ /\ ~infoOk
                                                 /\ \/ msg.mtype = CEPOCH
                                                    \/ msg.mtype = ACKEPOCH
                                                    \/ msg.mtype = ACKLD
                                                    \/ msg.mtype = ACK
                                        \/ /\ IsFollower(i)
                                           /\ LET infoOk == IsMyLeader(i, j) 
                                              IN
                                              \/ msg.mtype = CEPOCH
                                              \/ msg.mtype = ACKEPOCH
                                              \/ msg.mtype = ACKLD
                                              \/ msg.mtype = ACK
                                              \/ /\ ~infoOk
                                                 /\ \/ msg.mtype = NEWEPOCH
                                                    \/ msg.mtype = NEWLEADER
                                                    \/ msg.mtype = COMMITLD
                                                    \/ msg.mtype = PROPOSE
                                                    \/ msg.mtype = COMMIT   
                                        \/ IsLooking(i)
                                  /\ Discard(j, i)
        \* /\ violatedInvariants' = violatedInvariants
        \* /\ violatedInvariants' = [violatedInvariants EXCEPT !.messageIllegal = TRUE]
        /\ UNCHANGED <<serverVars, leaderVars, followerVars, electionVars, proposalMsgsLog, epochLeader>>
----------------------------------------------------------------------------

(* Election *)
UpdateLeaderAction == TRUE /\ \E i \in Server:    UpdateLeader(i)
FollowLeaderMyselfAction == TRUE /\ \E i \in Server:    FollowLeaderMyself(i)
FollowLeaderOtherAction == TRUE /\ \E i \in Server:    FollowLeaderOther(i)

(* Abnormal situations like failure, network disconnection *)
TimeoutWithQuorumAction == TRUE /\ \E i, j \in Server : TimeoutWithQuorum(i, j)
TimeoutNoQuorumAction == TRUE /\ \E i, j \in Server : TimeoutNoQuorum(i, j)

RestartAction == TRUE /\ \E i \in Server:    Restart(i)

(* Zab module - Discovery part *)
ConnectAndFollowerSendCEPOCHAction == TRUE /\ \E i, j \in Server: ConnectAndFollowerSendCEPOCH(i, j)
LeaderProcessCEPOCHAction == TRUE /\ \E i, j \in Server: LeaderProcessCEPOCH(i, j)
FollowerProcessNEWEPOCHAction == TRUE /\ \E i, j \in Server: FollowerProcessNEWEPOCH(i, j)

(* Zab module - Synchronization *)
LeaderProcessACKEPOCHHasntBroadcastAction == TRUE /\ \E i, j \in Server: LeaderProcessACKEPOCHHasntBroadcast(i, j)
LeaderProcessACKEPOCHHasBroadcastAction == TRUE /\ \E i, j \in Server: LeaderProcessACKEPOCHHasBroadcast(i, j)
FollowerProcessNEWLEADERAction == TRUE /\ \E i, j \in Server: FollowerProcessNEWLEADER(i, j)
FollowerProcessNEWLEADERNewIterationAction == TRUE /\ \E i, j \in Server: FollowerProcessNEWLEADERNewIteration(i, j)
LeaderProcessACKLDHasntBroadcastAction == TRUE /\ \E i, j \in Server: LeaderProcessACKLDHasntBroadcast(i, j)
LeaderProcessACKLDHasBroadcastAction == TRUE /\ \E i, j \in Server: LeaderProcessACKLDHasBroadcast(i, j)
FollowerProcessCOMMITLDAction == TRUE /\ \E i, j \in Server: FollowerProcessCOMMITLD(i, j)

(* Zab module - Broadcast part *)
LeaderProcessRequestAction == TRUE /\ \E i \in Server:    LeaderProcessRequest(i)
LeaderBroadcastPROPOSEAction == TRUE /\ \E i \in Server:    LeaderBroadcastPROPOSE(i)
FollowerProcessPROPOSEAction == TRUE /\ \E i, j \in Server: FollowerProcessPROPOSE(i, j)
LeaderProcessACKAction == TRUE /\ \E i, j \in Server: LeaderProcessACK(i, j)
LeaderProcessACKAlreadyCommittedAction == TRUE /\ \E i, j \in Server: LeaderProcessACKAlreadyCommitted(i, j)
FollowerProcessCOMMITAction == TRUE /\ \E i, j \in Server: FollowerProcessCOMMIT(i, j)

(* An action used to judge whether there are redundant messages in network *)
FilterNonexistentMessageAction == TRUE /\ \E i \in Server:    FilterNonexistentMessage(i)

\* Complete transition relation.
Next == 
    \/ UpdateLeaderAction
    \/ FollowLeaderMyselfAction
    \/ FollowLeaderOtherAction
    \* Disable these actions for now.
    \* \/ TimeoutWithQuorumAction
    \* \/ TimeoutNoQuorumAction
    \* \/ RestartAction
    \/ ConnectAndFollowerSendCEPOCHAction
    \/ LeaderProcessCEPOCHAction
    \/ FollowerProcessNEWEPOCHAction
    \/ LeaderProcessACKEPOCHHasntBroadcastAction
    \* \/ LeaderProcessACKEPOCHHasBroadcastAction
    \/ FollowerProcessNEWLEADERAction
    \/ FollowerProcessNEWLEADERNewIterationAction
    \/ LeaderProcessACKLDHasntBroadcastAction
    \* \/ LeaderProcessACKLDHasBroadcastAction
    \/ FollowerProcessCOMMITLDAction
    \/ LeaderProcessRequestAction
    \/ LeaderBroadcastPROPOSEAction
    \/ FollowerProcessPROPOSEAction
    \/ LeaderProcessACKAction
    \* \/ LeaderProcessACKAlreadyCommittedAction
    \/ FollowerProcessCOMMITAction
    \* \/ FilterNonexistentMessageAction

\* The complete specification.
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Define safety properties of Zab.

\* Inv1 == ~(\E s \in Server : state[s] = LEADING)
DebugInv1 == ~(\E s \in Server : state[s] = LEADING /\ Len(history[s]) > 0 /\ lastCommitted[s].index > 0)

\* ShouldNotBeTriggered == \A p \in DOMAIN violatedInvariants: violatedInvariants[p] = FALSE

\* There is most one established leader for a certain epoch.
H_Leadership1 == \A i, j \in Server:
                   /\ IsLeader(i) /\ zabState[i] \in {SYNCHRONIZATION, BROADCAST}
                   /\ IsLeader(j) /\ zabState[j] \in {SYNCHRONIZATION, BROADCAST}
                   /\ currentEpoch[i] = currentEpoch[j]
                  => i = j

Leadership2 == \A epoch \in 1..MAXEPOCH: Cardinality(epochLeader[epoch]) <= 1

\* PrefixConsistency: The prefix that have been committed 
\* in history in any process is the same.
H_PrefixConsistency == 
    \A i, j \in Server:
        LET smaller == Minimum({lastCommitted[i].index, lastCommitted[j].index}) IN
            (smaller > 0) =>
                (\A index \in 1..smaller: 
                    /\ index \in DOMAIN history[i]
                    /\ index \in DOMAIN history[j]
                    /\ TxnEqual(history[i][index], history[j][index]))

\* Integrity: If some follower delivers one transaction, then some primary has broadcast it.
Integrity == \A i \in Server:
                /\ IsFollower(i)
                /\ lastCommitted[i].index > 0
                => \A idx \in 1..lastCommitted[i].index: \E proposal \in proposalMsgsLog:
                    LET txn_proposal == [ zxid  |-> proposal.zxid,
                                          value |-> proposal.data ]
                    IN  TxnEqual(history[i][idx], txn_proposal)

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
LocalPrimaryOrder == LET p_set(i, e) == {p \in proposalMsgsLog: /\ p.source = i 
                                                                /\ p.epoch  = e }
                         txn_set(i, e) == { [ zxid  |-> p.zxid, 
                                              value |-> p.data ] : p \in p_set(i, e) }
                     IN \A i \in Server: \A e \in 1..currentEpoch[i]:
                         \/ Cardinality(txn_set(i, e)) < 2
                         \/ /\ Cardinality(txn_set(i, e)) >= 2
                            /\ \E txn1, txn2 \in txn_set(i, e):
                             \/ TxnEqual(txn1, txn2)
                             \/ /\ ~TxnEqual(txn1, txn2)
                                /\ LET TxnPre  == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn2 ELSE txn1
                                       TxnNext == IF ZxidCompare(txn1.zxid, txn2.zxid) THEN txn1 ELSE txn2
                                   IN \A j \in Server: /\ lastCommitted[j].index >= 2
                                                       /\ \E idx \in 1..lastCommitted[j].index: 
                                                            TxnEqual(history[j][idx], TxnNext)
                                        => \E idx2 \in 1..lastCommitted[j].index: 
                                            /\ TxnEqual(history[j][idx2], TxnNext)
                                            /\ idx2 > 1
                                            /\ \E idx1 \in 1..(idx2 - 1): 
                                                TxnEqual(history[j][idx1], TxnPre)

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

\* 
\* Helper lemma invariants
\* 

\* Is log li a prefix of log lj.
IsPrefix(li,lj) == 
    /\ Len(li) <= Len(lj)
    /\ SubSeq(li, 1, Len(li)) = SubSeq(lj, 1, Len(li))

\* Extract only zxid and value from a given history.
TxnHistory(h) == [i \in DOMAIN h |-> [zxid |-> h[i].zxid, value |-> h[i].value] ]

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

\* If a NEWLEADER message has been sent from a leader N in epoch E, then 
\* that message's history must be a prefix of the leader's history in epoch E, w.r.t the txns
\* that appear in that history i.e. (zxid, value) pairs.
H_NEWLEADERMsgIsPrefixOfSenderLeader == 
    \A i,j \in Server : 
        (/\ PendingNEWLEADER(i,j)
         /\ msgs[j][i][1].mepoch = currentEpoch[j]) => 
            (/\ IsPrefix(TxnHistory(msgs[j][i][1].mhistory), TxnHistory(history[j])))

H_NEWLEADERIncomingImpliesLastCommittedBound == 
    \A i,j \in Server : 
        PendingNEWLEADER(i,j) => 
            (\* lastCommitted on node is <= length of incoming history.
             lastCommitted[i].index <= Len(msgs[j][i][1].mhistory))

\* If a COMMIT message has been sent by a node, then the zxid referred to by that COMMIT
\* must be present in the sender's history, and its lastCommitted must cover that zxid in its history.
H_COMMITSentByNodeImpliesZxidInLog == 
    \A i,j \in Server : 
        PendingCOMMIT(i,j) =>   
            \E idx \in DOMAIN history[j] : 
                /\ history[j][idx].zxid = msgs[j][i][1].mzxid  
                /\ lastCommitted[j].index >= idx

\* TODO: Work on this further to develop a more unified lemma for establishing zxid uniqueness throughout the whole system.
\* All messages currently in the system
\* AllMsgs == {UNION {m : m \in DOMAIN msgs[i][j]} : i,j \in Server \X Server}

\* AllACKs == {m \in AllMsgs : m.mtype = "ACK"}

\* \* Set of all [zxid: zxid, value: value) records/pairs that exist in the system. 
\* AllSystemsZxids == 
\*     UNION { TxnHistory(history[i]) : i \in Server } \cup
\*     {m.mzxid}

\* Any two transactions with the same zxid must be equal.
\* Note: this must hold no matter where a zxid appears i.e. in a message or on a local node.
H_TxnWithSameZxidEqual == 
    \A i,j \in Server : 
        \A idxi \in (DOMAIN history[i]) :
        \A idxj \in (DOMAIN history[j]) : 
            ZxidEqual(history[i][idxi].zxid, history[j][idxj].zxid) =>
                TxnEqual(history[i][idxi], history[j][idxj])

H_TxnWithSameZxidEqualInPeerHistory == 
    \A s \in Server :
    \A x,y \in ackeRecv[s] :
        \A ix \in DOMAIN x.peerHistory :
        \A iy \in DOMAIN y.peerHistory :
            ZxidEqual(x.peerHistory[ix].zxid, y.peerHistory[iy].zxid) =>
                TxnEqual(x.peerHistory[ix], y.peerHistory[iy])

H_TxnWithSameZxidEqualLocalToPeerHistory == 
    \A s \in Server :
    \A x \in ackeRecv[s] :
    \A i \in Server : 
    \A idxi \in (DOMAIN history[i]) :
        \A ix \in DOMAIN x.peerHistory :
            ZxidEqual(x.peerHistory[ix].zxid, history[i][idxi].zxid) =>
                TxnEqual(x.peerHistory[ix], history[i][idxi])

\* If zxid matches between any two histories in messages in network, 
\* then the transactions must be equal.
H_TxnWithSameZxidEqualInMessages == 
    \A i,j,i2,j2 \in Server :
        \A idx \in DOMAIN msgs[i][j] : 
        \A idx2 \in DOMAIN msgs[i2][j2] : 
            (/\ "mhistory" \in DOMAIN msgs[i][j][idx]
             /\ "mhistory" \in DOMAIN msgs[i2][j2][idx2]) =>
                \A h1 \in DOMAIN msgs[i][j][idx].mhistory :
                \A h2 \in DOMAIN msgs[i2][j2][idx2].mhistory : 
                    ZxidEqual(msgs[i][j][idx].mhistory[h1].zxid, msgs[i2][j2][idx2].mhistory[h2].zxid) =>
                    TxnEqual(msgs[i][j][idx].mhistory[h1], msgs[i2][j2][idx2].mhistory[h2])

H_TxnWithSameZxidEqualInPROPOSEMessages == 
    \A i,j,i2,j2 \in Server :
    \A idx \in (DOMAIN msgs[i][j]) : 
    \A idx2 \in (DOMAIN msgs[i2][j2]) : 
        (/\ msgs[i][j][idx].mtype = PROPOSE 
         /\ msgs[i2][j2][idx2].mtype = PROPOSE) =>
            (ZxidEqual(msgs[i][j][idx].mzxid, msgs[i2][j2][idx2].mzxid) => 
                (msgs[i][j][idx].mdata = msgs[i2][j2][idx2].mdata))

H_TxnWithSameZxidEqualBetweenLocalHistoryAndMessages == 
    \A i,j,i1 \in Server :
        \A idx \in DOMAIN msgs[i][j] : 
        \A idx2 \in DOMAIN history[i1] : 
            (/\ "mhistory" \in DOMAIN msgs[i][j][idx]) =>
                \A h1 \in DOMAIN msgs[i][j][idx].mhistory :
                \A h2 \in DOMAIN history[i1]: 
                    ZxidEqual(msgs[i][j][idx].mhistory[h1].zxid, history[i1][h2].zxid) =>
                    TxnEqual(msgs[i][j][idx].mhistory[h1], history[i1][h2])

H_TxnWithSameZxidEqualBetweenLocalHistoryAndPROPOSEMessages == 
    \A i,j,i1 \in Server :
        \A idx \in DOMAIN msgs[i][j] : 
        \A idx2 \in DOMAIN history[i1] : 
            (msgs[i][j][idx].mtype = PROPOSE) =>
                \A h2 \in DOMAIN history[i1] : 
                    ZxidEqual(msgs[i][j][idx].mzxid, history[i1][h2].zxid) =>
                    msgs[i][j][idx].mdata = history[i1][h2].value

\* If a PROPOSE message has been sent with a particular zxid, then this zxid must be present
\* in the sender's log, and the sender must be a leader.
H_PROPOSEMsgSentByNodeImpliesZxidInLog == 
    \A i,j \in Server : 
        (PendingPROPOSE(i,j)) => 
            /\ IsLeader(j)
            /\ zabState[j] = BROADCAST
            /\ \E idx \in DOMAIN history[j] : history[j][idx].zxid = msgs[j][i][1].mzxid

\* If a COMMITLD message has been sent by a node, then the zxid in this message must be committed 
\* in the sender's history.
H_COMMITLDSentByNodeImpliesZxidCommittedInLog == 
    \A i,j \in Server : 
        (/\ PendingCOMMITLD(i,j)
         /\ ~ZxidEqual(msgs[j][i][1].mzxid, <<0,0>>)) => 
            \E idx \in DOMAIN history[j] : 
                /\ history[j][idx].zxid = msgs[j][i][1].mzxid  
                /\ lastCommitted[j].index >= idx

\* If a node is LOOKING, then it must have an empty input buffer.
H_NodeLOOKINGImpliesEmptyInputBuffer == 
    \A i \in Server : 
        (state[i] = LOOKING) => 
            \A j \in Server : msgs[j][i] = << >>

\* If a node is LOOKING, then it must be in DISCOVERY or ELECTION and have an empty input buffer.
H_NodeLOOKINGImpliesELECTIONorDISCOVERY == 
    \A i \in Server : (state[i] = LOOKING) => (zabState[i] \in {ELECTION, DISCOVERY})

H_CommittedEntryExistsInNEWLEADERHistory ==
    \A s \in Server : 
    \A idx \in DOMAIN history[s] : 
        (idx <= lastCommitted[s].index) =>
            (\A i,j \in Server : 
                (/\ PendingNEWLEADER(i,j)
                \*  /\ zabState[j] \in {DISCOVERY, SYNCHRONIZATION} 
                 ) =>
                    (\E idx2 \in DOMAIN msgs[j][i][1].mhistory : 
                        /\ idx2 = idx
                        /\ TxnEqual(history[s][idx], msgs[j][i][1].mhistory[idx2])))

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

\* If a history entry is covered by some lastCommitted, then it must be present in 
\* the initial history as determined by a received quorum of ACKEPOCH messages.
H_CommittedEntryExistsInACKEPOCHQuorumHistory ==
    \A s \in Server : 
    \A idx \in DOMAIN history[s] : 
    \A i,j \in Server :
        \* Entry is covered by lastCommitted on s.
        (/\ idx <= lastCommitted[s].index
         /\ PendingACKEPOCH(i, j)) => 
            \* Server i is a leader who is about to receive an ACK-E quorum and compute the new initial history.
            \* This initial history must contain the committed entry. 
            (LET msg == msgs[j][i][1]
                ackeRecvUpdated == [ackeRecv EXCEPT ![i] = UpdateAckeRecv(@, j, msg.mepoch, msg.mhistory) ] IN
                (
                    /\ zabState[i] \in {ELECTION, DISCOVERY}
                    /\ state[i] = LEADING
                    /\ IsQuorum({a.sid: a \in ackeRecvUpdated[i]})
                ) => 
                    LET initHistory == DetermineInitialHistoryFromArg(ackeRecvUpdated, i) IN
                    \E k \in DOMAIN initHistory : 
                        /\ k = idx
                        /\ TxnEqual(history[s][idx], initHistory[k]))

H_ServerInEntryAckSidImpliesHasEntry == 
    \A s,t \in Server : 
    \A ind \in DOMAIN history[s]:
        (state[s] = LEADING /\ t \in history[s][ind].ackSid) =>
            \E indt \in DOMAIN history[t] : 
                TxnEqual(history[t][indt], history[s][ind])

\* The learner of a leader in BROADCAST must also be in BROADCAST and a follower.
H_LeaderInBROADCASTImpliesLearnerInBROADCAST == 
    \A i,j \in Server : 
        (/\ IsLeader(i) 
         /\ zabState[i] = BROADCAST
         /\ j \in learners[i] 
         /\ j # i ) => 
            \* TODO: Think about this condition more.
            \* /\ (zabState[j] # BROADCAST) => msgs[j][i] # <<>>
            /\ IsFollower(j)

H_PROPOSEMsgInFlightImpliesNodesInBROADCAST == 
    \A i,j \in Server : 
        (PendingPROPOSE(j,i)) =>
            /\ zabState[i] = BROADCAST
            /\ zabState[j] = BROADCAST
            /\ IsFollower(j)
            /\ IsLeader(i)

\* If an ACK message is in flight, there must be a leader and they
\* are in BROADCAST.
H_ACKMsgInFlightImpliesNodesInBROADCAST == 
    \A i,j \in Server : 
        (PendingACK(i,j)) =>
            /\ zabState[i] = BROADCAST
            /\ zabState[j] = BROADCAST
            /\ IsFollower(j)
            /\ IsLeader(i)



\* If a leader is in BROADCAST, no NEWLEADER messages should be in-flight
H_LeaderinBROADCASTImpliesNoNEWLEADERInFlight == 
  (\E s \in Server : state[s] = LEADING /\ zabState = BROADCAST) =>
    (\A i,j \in Server :  ~PendingNEWLEADER(i,j))

\* If an ACK message exists from S for a given zxid, then that zxid must be present in the sender's history.
H_ACKMsgImpliesZxidInLog == 
    \A i,j \in Server : 
        PendingACK(i,j) => 
            \E idx \in DOMAIN history[j] : 
                history[j][idx].zxid = msgs[j][i][1].mzxid

\* If an ACKLD message exists from S for a given zxid, then that zxid must be present in the sender's history.
\* Also, this zxid should exist on a quorum (?), since it must be committed?
H_ACKLDMsgImpliesZxidInLog == 
    \A i,j \in Server : 
        (PendingACKLD(i,j) /\ ZxidCompare(msgs[j][i][1].mzxid, <<0,0>>)) => 
            /\ \E idx \in DOMAIN history[j] : history[j][idx].zxid = msgs[j][i][1].mzxid
            \* Entry exists on a quorum, since it must be committed.
            /\ \E Q \in Quorums : 
               \A n \in Q : 
               \E ic \in DOMAIN history[n] : 
                    msgs[j][i][1].mzxid = history[n][ic].zxid

\* A node's lastCommitted index must always be <= its history length.
H_NodeHistoryBoundByLastCommittedIndex == 
    \A s \in Server : lastCommitted[s].index <= Len(history[s])

\* If a follower has sent ACKLD to a leader, then its log must match the leader's log.
H_ACKLDSentByFollowerImpliesLogMatch == 
    \A i,j \in Server : 
        (/\ PendingACKLD(i,j)
         /\ IsLeader(i)) => 
            IsPrefix(TxnHistory(history[j]), TxnHistory(history[i]))

\* If an entry is committed, then it should be contained in a leader's history.
H_CommittedEntryExistsInLeaderHistory == 
    \A i,j \in Server : 
        \A idx \in DOMAIN history[i] : 
            (/\ idx <= lastCommitted[i].index
             /\ IsLeader(j)
             /\ zabState[j] = SYNCHRONIZATION) => 
                \* Committed entry exists in leader's history.
                \E idx2 \in DOMAIN history[j] : 
                    /\ idx2 = idx
                    /\ history[j][idx2].zxid = history[i][idx].zxid

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

\* Leader in BROADCAST phase must contain all history entries created in its epoch.
H_LeaderInBroadcastImpliesAllHistoryEntriesInEpoch == 
    \A i,j \in Server : 
    \A idx \in DOMAIN history[j] :
        (/\ IsLeader(i)
         /\ zabState[i] = BROADCAST
         /\ history[j][idx].zxid[1] = currentEpoch[i]) => 
            \* Entry is in leader's history.
            \E idx2 \in DOMAIN history[i] : ZxidEqual(history[i][idx2].zxid, history[j][idx].zxid)

----------------------------------------------------------

\* Model checking stuff.

Symmetry == Permutations(Server)

NextUnchanged == UNCHANGED vars

\* Sum the elements in the range of a function.
RECURSIVE SumFnRange(_)
SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
  LET x == CHOOSE x \in DOMAIN f : TRUE
    IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s))

RECURSIVE SetSum(_)
SetSum(set) == IF set = {} THEN 0 ELSE
  LET x == CHOOSE x \in set: TRUE
    IN x + SetSum(set \ {x})

CTICost == 
    SumFnRange([s \in Server |-> Len(history[s])]) +
    SumFnRange(currentEpoch) +
    SumFnRange([s \in Server |-> Cardinality(ackeRecv[s])]) +
    SumFnRange([s \in Server |-> Cardinality(cepochRecv[s])]) +
    SumFnRange([<<s,t>> \in Server \X Server |-> Len(msgs[s][t])])

=============================================================================
\* Modification History
\* Last modified Tue Jan 31 20:40:11 CST 2023 by huangbinyu
\* Last modified Sat Dec 11 22:31:08 CST 2021 by Dell
\* Created Thu Dec 02 20:49:23 CST 2021 by Dell