------------------------- MODULE BakeryDistributed -------------------------
(***************************************************************************)
(* This is the PlusCal specification of the distributed bakery algorithm   *)
(* in the paper                                                            *)
(*                                                                         *)
(*    Deconstructing the Bakery to Build a Distributed State Machine       *)
(*                                                                         *)
(* We assume here that you have read the BakeryDeconstructed               *)
(* specification, whose comments explain the structure of this PlusCal     *)
(* translation of the pseudo-code in the paper, and how it was model       *)
(* checked.                                                                *)
(*                                                                         *)
(* The statements in gray in the paper's pseudo-code, which involve the    *)
(* unnecessary variable localCh, are identified here by lines that end     *)
(* with the comment ERASABLE in the PlusCal code and where localCh appears *)
(* in the TypeOK invariant.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences

q \ll r == \/ q[1] < r[1]
           \/ /\ q[1] = r[1]
              /\ q[2] < r[2]

CONSTANT N
ASSUME N \in Nat \ {0}

Nodes == 1..N
OtherNodes(i) == Nodes \ {i}
ProcIds == {<<i>> : i \in Nodes}
SubProcs == {p \in Nodes \X Nodes : p[1] # p[2]}
MsgProcs == {p \in Nodes \X Nodes \X {"msg"} : p[1] # p[2]}
SubProcsOf(i) == {p \in SubProcs : p[1] = i} 

ack  == -1

(***************************************************************************
algo
Decon {
  variables number = [i \in Nodes |-> 0], 
            localNum = [i \in Nodes |-> [j \in OtherNodes(i) |-> 0]] ,
            localCh  = [i \in Nodes |-> [j \in OtherNodes(i) |-> 0]] ,  (* ERASABLE *)
            ackRcvd  = [i \in Nodes |-> [j \in OtherNodes(i) |-> 0]] ,
            q = [i \in Nodes |-> [j \in OtherNodes(i) |-> << >>]] 
  
  fair process (main \in ProcIds) {
    ncs:- while (TRUE) {
            skip ; (* noncritical section *)
         M: await \A p \in SubProcsOf(self[1]) : pc[p] = "L0" ;
            with (v \in {n \in Nat \ {0} : 
                           \A j \in OtherNodes(self[1]) : 
                               n > localNum[self[1]][j]}) {
               number[self[1]] := v;
               q[self[1]] := [j \in OtherNodes(self[1]) 
                                |-> Append(q[self[1]][j],v)]
            } ;
         L: await \A p \in SubProcsOf(self[1]) : pc[p] = "ch" ;
        cs: skip ; (* critical section *)
         P: ackRcvd[self[1]] := [j \in OtherNodes(self[1]) |-> 0] ;
            number[self[1]] := 0 ;
            q[self[1]] := [j \in OtherNodes(self[1]) 
                             |-> Append(q[self[1]][j],0)] 
          }
  }
  
  fair process (sub \in SubProcs) {
    ch: while (TRUE) {
           await pc[<<self[1]>>] = "M" ;
           localCh[self[2]][self[1]] := 1 ;  (* ERASABLE *)
      L0:  await pc[<<self[1]>>] = "L" ;
           await ackRcvd[self[1]][self[2]] = 1 ;
           localCh[self[2]][self[1]] := 0 ;      (* ERASABLE *)
      L2:  await localCh[self[1]][self[2]] = 0 ; (* ERASABLE *)
      L3:  await \/ localNum[self[1]][self[2]] = 0 
                 \/ <<number[self[1]], self[1]>> \ll 
                      <<localNum[self[1]][self[2]], self[2]>> 
        }
  }
  
  fair process (msg \in MsgProcs) {
    wr: while (TRUE) {
          await q[self[2]][self[1]] # << >>;
          with (v = Head(q[self[2]][self[1]])) {
            if (v = ack) {ackRcvd[self[1]][self[2]] := 1}
            else {localNum[self[1]][self[2]] := v } ;
            if (v \in {0, ack}) {
               q[self[2]][self[1]] := Tail(q[self[2]][self[1]]) }
            else {q[self[2]][self[1]] := Tail(q[self[2]][self[1]]) || 
                  q[self[1]][self[2]] := Append(q[self[1]][self[2]], ack) } 
            }
        }
  }
}



 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "9709f4e9" /\ chksum(tla) = "8b3daef")
VARIABLES number, localNum, localCh, ackRcvd, q, pc

vars == << number, localNum, localCh, ackRcvd, q, pc >>

ProcSet == (ProcIds) \cup (SubProcs) \cup (MsgProcs)

Init == (* Global variables *)
        /\ number = [i \in Nodes |-> 0]
        /\ localNum = [i \in Nodes |-> [j \in OtherNodes(i) |-> 0]]
        /\ localCh = [i \in Nodes |-> [j \in OtherNodes(i) |-> 0]]
        /\ ackRcvd = [i \in Nodes |-> [j \in OtherNodes(i) |-> 0]]
        /\ q = [i \in Nodes |-> [j \in OtherNodes(i) |-> << >>]]
        /\ pc = [self \in ProcSet |-> CASE self \in ProcIds -> "ncs"
                                        [] self \in SubProcs -> "ch"
                                        [] self \in MsgProcs -> "wr"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "M"]
             /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>

M(self) == /\ pc[self] = "M"
           /\ \A p \in SubProcsOf(self[1]) : pc[p] = "L0"
           /\ \E v \in {n \in Nat \ {0} :
                          \A j \in OtherNodes(self[1]) :
                              n > localNum[self[1]][j]}:
                /\ number' = [number EXCEPT ![self[1]] = v]
                /\ q' = [q EXCEPT ![self[1]] = [j \in OtherNodes(self[1])
                                                  |-> Append(q[self[1]][j],v)]]
           /\ pc' = [pc EXCEPT ![self] = "L"]
           /\ UNCHANGED << localNum, localCh, ackRcvd >>

L(self) == /\ pc[self] = "L"
           /\ \A p \in SubProcsOf(self[1]) : pc[p] = "ch"
           /\ pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P"]
            /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>

P(self) == /\ pc[self] = "P"
           /\ ackRcvd' = [ackRcvd EXCEPT ![self[1]] = [j \in OtherNodes(self[1]) |-> 0]]
           /\ number' = [number EXCEPT ![self[1]] = 0]
           /\ q' = [q EXCEPT ![self[1]] = [j \in OtherNodes(self[1])
                                             |-> Append(q[self[1]][j],0)]]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ UNCHANGED << localNum, localCh >>

main(self) == ncs(self) \/ M(self) \/ L(self) \/ cs(self) \/ P(self)

ch(self) == /\ pc[self] = "ch"
            /\ pc[<<self[1]>>] = "M"
            /\ localCh' = [localCh EXCEPT ![self[2]][self[1]] = 1]
            /\ pc' = [pc EXCEPT ![self] = "L0"]
            /\ UNCHANGED << number, localNum, ackRcvd, q >>

L0(self) == /\ pc[self] = "L0"
            /\ pc[<<self[1]>>] = "L"
            /\ ackRcvd[self[1]][self[2]] = 1
            /\ localCh' = [localCh EXCEPT ![self[2]][self[1]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << number, localNum, ackRcvd, q >>

L2(self) == /\ pc[self] = "L2"
            /\ localCh[self[1]][self[2]] = 0
            /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>

L3(self) == /\ pc[self] = "L3"
            /\ \/ localNum[self[1]][self[2]] = 0
               \/ <<number[self[1]], self[1]>> \ll
                    <<localNum[self[1]][self[2]], self[2]>>
            /\ pc' = [pc EXCEPT ![self] = "ch"]
            /\ UNCHANGED << number, localNum, localCh, ackRcvd, q >>

sub(self) == ch(self) \/ L0(self) \/ L2(self) \/ L3(self)

wr(self) == /\ pc[self] = "wr"
            /\ q[self[2]][self[1]] # << >>
            /\ LET v == Head(q[self[2]][self[1]]) IN
                 /\ IF v = ack
                       THEN /\ ackRcvd' = [ackRcvd EXCEPT ![self[1]][self[2]] = 1]
                            /\ UNCHANGED localNum
                       ELSE /\ localNum' = [localNum EXCEPT ![self[1]][self[2]] = v]
                            /\ UNCHANGED ackRcvd
                 /\ IF v \in {0, ack}
                       THEN /\ q' = [q EXCEPT ![self[2]][self[1]] = Tail(q[self[2]][self[1]])]
                       ELSE /\ q' = [q EXCEPT ![self[2]][self[1]] = Tail(q[self[2]][self[1]]),
                                              ![self[1]][self[2]] = Append(q[self[1]][self[2]], ack)]
            /\ pc' = [pc EXCEPT ![self] = "wr"]
            /\ UNCHANGED << number, localCh >>

msg(self) == wr(self)

Next == (\E self \in ProcIds: main(self))
           \/ (\E self \in SubProcs: sub(self))
           \/ (\E self \in MsgProcs: msg(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcIds : WF_vars((pc[self] # "ncs") /\ main(self))
        /\ \A self \in SubProcs : WF_vars(sub(self))
        /\ \A self \in MsgProcs : WF_vars(msg(self))

\* END TRANSLATION 
-----------------------------------------------------------------------------
TypeOK ==  /\ number \in [Nodes -> Nat]
           /\ /\ DOMAIN localNum = Nodes
              /\ \A i \in Nodes : localNum[i] \in [OtherNodes(i) -> Nat]
           /\ /\ DOMAIN localCh = Nodes                                    (* ERASABLE *)
              /\ \A i \in Nodes : localCh[i] \in [OtherNodes(i) -> {0,1}]  (* ERASABLE *)
           /\ /\ DOMAIN ackRcvd = Nodes
              /\ \A i \in Nodes : ackRcvd[i] \in [OtherNodes(i) -> {0,1}]
           /\ /\ DOMAIN q = Nodes
              /\ \A i \in Nodes : q[i] \in [OtherNodes(i) -> Seq(Nat \cup {ack})]
           /\ /\ DOMAIN pc = ProcSet
              /\ \A p \in ProcSet:
                   CASE p \in ProcIds -> pc[p] \in {"ncs", "M", "L", "cs", "P"}
                     [] p \in SubProcs -> pc[p] \in {"ch", "L0", "L2", "L3"}
                     [] p \in MsgProcs -> pc[p] = "wr"


H_MutualExclusion == \A p, r \in ProcIds : (p # r) => ({pc[p],pc[r]} # {"cs"})

StarvationFree == \A p \in ProcIds : (pc[p] = "M") ~> (pc[p] = "cs")
-----------------------------------------------------------------------------
TestMaxNum == 6
TestNat == 0..(TestMaxNum + 1)

(***************************************************************************)
(*                             TEST RESULTS                                *)
(*                                                                         *)
(* TLC has tested that TypeOK and MutualExclusion are invariants of the    *)
(* algorithm, and that the algorithm satisfies the temporal property       *)
(* StarvationFree.  As a sanity check, some smaller models were used to    *)
(* check that, if fairness is not disabled for the ncs action, then the    *)
(* algorithm satisfies the following property, which asserts that every    *)
(* process executes the critical section infinitely many times.            *)
(*                                                                         *)
(*    \A i \in Procs : []<>(pc[<<i>>] = "cs")                              *)
(*                                                                         *)
(* The largest model that was tested was for N = 3 and TestMaxNum = 6.  It *)
(* had 24,943,042 reachable states and was executed in a little less than  *)
(* 52 minutes on a 64-core machine using 55 worker threads.                *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Mon Aug 02 15:23:28 PDT 2021 by lamport
\* Created Tue Apr 27 10:33:38 PDT 2021 by lamport
