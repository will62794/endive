------------------------- MODULE GermanCache -------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NODE_NUM, DATA_NUM
ASSUME NODE_NUM \in Nat /\ NODE_NUM > 0
ASSUME DATA_NUM \in Nat /\ DATA_NUM > 0

NODE == 1..NODE_NUM
DATA == 1..DATA_NUM

CACHE_STATE == {"I", "S", "E"}
MSG_CMD == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

CACHE == [State: CACHE_STATE, Data: DATA]
MSG == [Cmd: MSG_CMD, Data: DATA]

VARIABLES
    Cache,  \* array [NODE] of CACHE
    Chan1,  \* array [NODE] of MSG, channels for Req*
    Chan2,  \* array [NODE] of MSG, channels for Gnt* and Inv
    Chan3,  \* array [NODE] of MSG, channels for InvAck
    InvSet, \* array [NODE] of BOOLEAN, nodes to be invalidated
    ShrSet, \* array [NODE] of BOOLEAN, nodes having S or E copies
    ExGntd, \* BOOLEAN, E copy has been granted
    CurCmd, \* MSG_CMD, current request command
    CurPtr, \* NODE, current request node
    MemData,\* DATA, memory data
    AuxData \* DATA, latest value of cache line

vars == <<Cache, Chan1, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Init ==
    /\ Cache = [i \in NODE |-> [State |-> "I", Data |-> 1]]
    /\ Chan1 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ Chan2 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ Chan3 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ InvSet = [i \in NODE |-> FALSE]
    /\ ShrSet = [i \in NODE |-> FALSE]
    /\ ExGntd = FALSE
    /\ CurCmd = "Empty"
    /\ CurPtr = 1
    /\ MemData = 1
    /\ AuxData = 1

TypeOK ==
    /\ Cache \in [NODE -> CACHE]
    /\ Chan1 \in [NODE -> MSG]
    /\ Chan2 \in [NODE -> MSG]
    /\ Chan3 \in [NODE -> MSG]
    /\ InvSet \in [NODE -> BOOLEAN]
    /\ ShrSet \in [NODE -> BOOLEAN]
    /\ ExGntd \in BOOLEAN
    /\ CurCmd \in MSG_CMD
    /\ CurPtr \in NODE
    /\ MemData \in DATA
    /\ AuxData \in DATA

(* Define state transitions here, following the Murphi model *)
SendReqS(i) ==
    /\ Chan1[i].Cmd = "Empty"
    /\ Cache[i].State = "I"
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "ReqS"]
    /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendReqE(i) ==
    /\ Chan1[i].Cmd = "Empty"
    /\ (Cache[i].State = "I" \/ Cache[i].State = "S")
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "ReqE"]
    /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvReqS(i) ==
    /\ CurCmd = "Empty"
    /\ Chan1[i].Cmd = "ReqS"
    /\ CurCmd' = "ReqS"
    /\ CurPtr' = i
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "Empty"]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

RecvReqE(i) ==
    /\ CurCmd = "Empty"
    /\ Chan1[i].Cmd = "ReqE"
    /\ CurCmd' = "ReqE"
    /\ CurPtr' = i
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "Empty"]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

SendInv(i) ==
    /\ Chan2[i].Cmd = "Empty"
    /\ InvSet[i] = TRUE
    /\ (CurCmd = "ReqE" \/ (CurCmd = "ReqS" /\ ExGntd = TRUE))
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"]
    /\ InvSet' = [InvSet EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<Cache, Chan1, Chan3, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendInvAck(i) ==
    /\ Chan2[i].Cmd = "Inv"
    /\ Chan3[i].Cmd = "Empty"
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ Chan3' = [Chan3 EXCEPT ![i] = [Cmd |-> "InvAck", Data |-> IF Cache[i].State = "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
    /\ Cache' = [Cache EXCEPT ![i].State = "I"]
    /\ UNCHANGED <<Chan1, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvInvAck(i) ==
    /\ Chan3[i].Cmd = "InvAck"
    /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i].Cmd = "Empty"]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    /\ IF ExGntd = TRUE
       THEN /\ ExGntd' = FALSE
            /\ MemData' = Chan3[i].Data
       ELSE /\ UNCHANGED ExGntd
            /\ UNCHANGED MemData
    /\ UNCHANGED <<Cache, Chan1, Chan2, InvSet, CurCmd, CurPtr, AuxData>>

SendGntS(i) ==
    /\ CurCmd = "ReqS"
    /\ CurPtr = i
    /\ Chan2[i].Cmd = "Empty"
    /\ ExGntd = FALSE
    /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntS", Data |-> MemData]]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    /\ CurCmd' = "Empty"
    /\ UNCHANGED <<Cache, Chan1, Chan3, InvSet, CurPtr, ExGntd, MemData, AuxData>>

SendGntE(i) ==
    /\ CurCmd = "ReqE"
    /\ CurPtr = i
    /\ Chan2[i].Cmd = "Empty"
    /\ ExGntd = FALSE
    /\ \A j \in NODE : ShrSet[j] = FALSE
    /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntE", Data |-> MemData]]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    /\ ExGntd' = TRUE
    /\ CurCmd' = "Empty"
    /\ UNCHANGED <<Cache, Chan1, Chan3, InvSet, CurPtr, MemData, AuxData>>

RecvGntS(i) ==
    /\ Chan2[i].Cmd = "GntS"
    /\ Cache' = [Cache EXCEPT ![i] = [State |-> "S", Data |-> Chan2[i].Data]]
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvGntE(i) ==
    /\ Chan2[i].Cmd = "GntE"
    /\ Cache' = [Cache EXCEPT ![i] = [State |-> "E", Data |-> Chan2[i].Data]]
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Store(i, d) ==
    /\ Cache[i].State = "E"
    /\ Cache' = [Cache EXCEPT ![i].Data = d]
    /\ AuxData' = d
    /\ UNCHANGED <<Chan1, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData>>

SendReqSAction == TRUE /\ \E i \in NODE : SendReqS(i)
SendReqEAction == TRUE /\ \E i \in NODE : SendReqE(i)
RecvReqSAction == TRUE /\ \E i \in NODE : RecvReqS(i)
RecvReqEAction == TRUE /\ \E i \in NODE : RecvReqE(i)
SendInvAction == TRUE /\ \E i \in NODE : SendInv(i)
SendInvAckAction == TRUE /\ \E i \in NODE : SendInvAck(i)
RecvInvAckAction == TRUE /\ \E i \in NODE : RecvInvAck(i)
SendGntSAction == TRUE /\ \E i \in NODE : SendGntS(i)
SendGntEAction == TRUE /\ \E i \in NODE : SendGntE(i)
RecvGntSAction == TRUE /\ \E i \in NODE : RecvGntS(i)
RecvGntEAction == TRUE /\ \E i \in NODE : RecvGntE(i)
StoreAction == TRUE /\ \E i \in NODE, d \in DATA : Store(i, d)

Next ==
    \/ SendReqSAction
    \/ SendReqEAction
    \/ RecvReqSAction
    \/ RecvReqEAction
    \/ SendInvAction
    \/ SendInvAckAction
    \/ RecvInvAckAction
    \/ SendGntSAction
    \/ SendGntEAction
    \/ RecvGntSAction
    \/ RecvGntEAction
    \/ StoreAction

\* Invariant properties.

CtrlProp1 ==
    \A i, j \in NODE :
        i /= j =>
            /\ (Cache[i].State = "E" => Cache[j].State = "I")


CtrlProp ==
    \A i, j \in NODE :
        i /= j =>
            /\ (Cache[i].State = "E" => Cache[j].State = "I")
            /\ (Cache[i].State = "S" => (Cache[j].State = "I" \/ Cache[j].State = "S"))

DataProp ==
    /\ (ExGntd = FALSE => MemData = AuxData)
    /\ \A i \in NODE :
        Cache[i].State /= "I" => Cache[i].Data = AuxData

Invariant ==
    /\ CtrlProp
    /\ DataProp

NextUnchanged == UNCHANGED vars
CTICost == 0
LInv41_2037_R0_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Cache[VARI].State = "I") \/ (~(Chan2[VARJ].Cmd = "GntE"))


LInv104_03a2_R0_0_I1 == \A VARI \in NODE : \A VARJ \in NODE : (Cache[VARJ].State = "I") \/ (~(Chan2[VARI].Cmd = "GntE"))
LInv3989_3a8e_R0_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARI].Cmd = "Empty") \/ (~(Cache[VARJ].State = "E") \/ (~(VARI # VARJ)))
LInv1011_61c6_R1_0_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARJ].Cmd = "Empty") \/ (~(Chan2[VARI].Cmd = "GntE") \/ (~(VARI # VARJ)))
LInv686_0d22_R1_1_I2 == \A VARI \in NODE : \A VARJ \in NODE : (Chan2[VARI].Cmd = "Empty") \/ (~(Chan2[VARJ].Cmd = "GntE") \/ (~(VARI # VARJ)))
LInv16_d756_R1_2_I1 == \A VARI \in NODE : (Cache[VARI].State = "I") \/ ((ShrSet[VARI]))
LInv11_513a_R2_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Cache[VARI].State = "E"))

LInv2775_6920_R2_3_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Cache[VARI].State = "E") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))
LInv1_85ad_R3_0_I1 == \A VARI \in NODE : (Chan2[VARI].Cmd = "Empty") \/ ((ShrSet[VARI]))
LInv4_a2c7_R3_1_I1 == \A VARI \in NODE : (ExGntd) \/ (~(Chan2[VARI].Cmd = "GntE"))
LInv3532_fc2f_R3_2_I2 == \A VARI \in NODE : \A VARJ \in NODE : ~(Chan2[VARI].Cmd = "GntE") \/ (~(InvSet[VARJ]) \/ (~(VARI # VARJ)))


====