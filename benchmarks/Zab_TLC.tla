---- MODULE Zab_TLC ----
EXTENDS Zab,TLC, Randomization

\* Model checking stuff.


SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

ZxidType == Epoch \X Nat

HistEntryType == [zxid: ZxidType, value: Nat, ackSid: SUBSET Server, epoch: Epoch]

HistTypeBounded == BoundedSeq(HistEntryType, MaxHistLen)

SetOfHistsTypeBounded == RandomSetOfSubsets(5, 5, HistTypeBounded)

AckeRecvTypeBounded == 
    RandomSetOfSubsets(1, 1, [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: HistTypeBounded]) \cup
    RandomSetOfSubsets(2, 2, [sid: Server, connected: BOOLEAN, peerLastEpoch: Nat, peerHistory: HistTypeBounded])

MsgCEPOCHType == [mtype: {CEPOCH}, mepoch: Epoch, msrc:Server, mdst:Server, morder: {0}]
MsgNEWEPOCHType == [mtype: {NEWEPOCH}, mepoch: Epoch,  msrc:Server, mdst:Server, morder: {0}]
MsgACKEPOCHType == [mtype: {ACKEPOCH}, mepoch: Epoch, mhistory: HistTypeBounded,  msrc:Server, mdst:Server, morder: {0}]
MsgNEWLEADERType == [mtype: {NEWLEADER}, mepoch: Epoch, mhistory: HistTypeBounded,  msrc:Server, mdst:Server, morder: {0}]
MsgACKLDType == [mtype: {ACKLD}, mzxid: ZxidType, msrc:Server, mdst:Server, morder: {0}]
MsgCOMMITLDType == [mtype: {COMMITLD}, mzxid: ZxidType, msrc:Server, mdst:Server, morder: {0}]
MsgPROPOSEType == [mtype: {PROPOSE}, mzxid: ZxidType, mdata: Value,  msrc:Server, mdst:Server, morder: {0}]
MsgACKType == [mtype: {ACK}, mzxid: ZxidType, msrc:Server, mdst:Server, morder: {0}]
MsgCOMMITType == [mtype: {COMMIT}, mzxid: ZxidType, msrc:Server, mdst:Server, morder: {0}]

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
    /\ msgs \in [Server -> [Server -> {<<>>}]]
    /\ CEPOCHmsgs \in RandomSetOfSubsets(2, 2, MsgCEPOCHType)
    /\ NEWEPOCHmsgs \in RandomSetOfSubsets(2, 2, MsgNEWEPOCHType)
    /\ ACKEPOCHmsgs \in RandomSetOfSubsets(2, 2, MsgACKEPOCHType)
    /\ NEWLEADERmsgs \in RandomSetOfSubsets(2, 2, MsgNEWLEADERType)
    /\ ACKLDmsgs \in RandomSetOfSubsets(2, 2, MsgACKLDType)
    /\ COMMITLDmsgs \in RandomSetOfSubsets(2, 2, MsgCOMMITLDType)
    /\ PROPOSEmsgs \in RandomSetOfSubsets(2, 2, MsgPROPOSEType)
    /\ ACKmsgs \in  RandomSetOfSubsets(2, 2, MsgACKType)
    /\ COMMITmsgs \in RandomSetOfSubsets(2, 2, MsgCOMMITType)



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

====