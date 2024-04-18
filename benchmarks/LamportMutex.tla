--------------------------- MODULE LamportMutex ----------------------------
(***************************************************************************)
(* TLA+ specification of Lamport's distributed mutual-exclusion algorithm  *)
(* that appeared as an example in                                          *)
(* L. Lamport:  Time, Clocks and the Ordering of Events in a Distributed   *)
(* System. CACM 21(7):558-565, 1978.                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC, Randomization

(***************************************************************************)
(* The parameter N represents the number of processes.                     *)
(* The parameter maxClock is used only for model checking in order to      *)
(* keep the state space finite.                                            *)
(***************************************************************************)
CONSTANT N, maxClock
CONSTANT Nats

ASSUME NType == N \in Nat
ASSUME maxClockType == maxClock \in Nat

Proc == 1 .. N
\* Clock == Nat \ {0}
Clock == Nats \ {0}
(***************************************************************************)
(* For model checking, add ClockConstraint as a state constraint to ensure *)
(* a finite state space and override the definition of Clock by            *)
(* 1 .. maxClock+1 so that TLC can evaluate the definition of Message.     *)
(***************************************************************************)

VARIABLES
  clock,    \* local clock of each process
  req,      \* requests received from processes (clock transmitted with request)
  ack,      \* acknowledgements received from processes
  network,  \* messages sent but not yet received
  crit      \* set of processes in critical section

(***************************************************************************)
(* Messages used in the algorithm.                                         *)
(***************************************************************************)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}

(***************************************************************************)
(* The type correctness predicate.                                         *)
(***************************************************************************)  
TypeOK ==
     (* clock[p] is the local clock of process p *)
  /\ clock \in [Proc -> Clock]
     (* req[p][q] stores the clock associated with request from q received by p, 0 if none *)
  /\ req \in [Proc -> [Proc -> Nats]]
     (* ack[p] stores the processes that have ack'ed p's request *)
  /\ ack \in [Proc -> SUBSET Proc]
     (* network[p][q]: queue of messages from p to q -- pairwise FIFO communication *)
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
     (* set of processes in critical section: should be empty or singleton *)
  /\ crit \in SUBSET Proc

TypeOKRandom ==
     (* clock[p] is the local clock of process p *)
  /\ clock \in [Proc -> Clock]
     (* req[p][q] stores the clock associated with request from q received by p, 0 if none *)
  /\ req \in [Proc -> [Proc -> Nats]]
     (* ack[p] stores the processes that have ack'ed p's request *)
  /\ ack \in [Proc -> SUBSET Proc]
     (* network[p][q]: queue of messages from p to q -- pairwise FIFO communication *)
  /\ network \in [Proc -> [Proc -> RandomSubset(4, BoundedSeq(Message, 2))]]
     (* set of processes in critical section: should be empty or singleton *)
  /\ crit \in SUBSET Proc


(***************************************************************************)
(* The initial state predicate.                                            *)
(***************************************************************************) 
Init ==
  /\ clock = [p \in Proc |-> 1]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> <<>> ]]
  /\ crit = {}

(***************************************************************************)
(* beats(p,q) is true if process p believes that its request has higher    *)
(* priority than q's request. This is true if either p has not received a  *)
(* request from q or p's request has a smaller clock value than q's.       *)
(* If there is a tie, the numerical process ID decides.                    *)
(***************************************************************************)
beats(p,q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q
  
(***************************************************************************)
(* Broadcast a message: send it to all processes except the sender.        *)
(***************************************************************************)
Broadcast(s, m) ==
  [r \in Proc |-> IF s=r THEN network[s][r] ELSE Append(network[s][r], m)]

(***************************************************************************)
(* Process p requests access to critical section.                          *)
(***************************************************************************)
Request(p) ==
  /\ req[p][p] = 0
  /\ req'= [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

(***************************************************************************)
(* Process p receives a request from q and acknowledges it.                *)
(***************************************************************************)
ReceiveRequest(p,q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "req"
         /\ req' = [req EXCEPT ![p][q] = c]
         /\ clock' = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1 ELSE @ + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage)]
         /\ UNCHANGED <<ack, crit>>

(***************************************************************************)
(* Process p receives an acknowledgement from q.                           *)
(***************************************************************************)      
ReceiveAck(p,q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ ack' = [ack EXCEPT ![p] = @ \union {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, req, crit>>

(**************************************************************************)
(* Process p enters the critical section.                                 *)
(**************************************************************************)
Enter(p) == 
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p,q)
  /\ crit' = crit \union {p}
  /\ UNCHANGED <<clock, req, ack, network>>
  
(***************************************************************************)
(* Process p exits the critical section and notifies other processes.      *)
(***************************************************************************)
Exit(p) ==
  /\ p \in crit
  /\ crit' = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock
 
(***************************************************************************)
(* Process p receives a release notification from q.                       *)
(***************************************************************************)
ReceiveRelease(p,q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req' = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, ack, crit>>

(***************************************************************************)
(* Next-state relation.                                                    *)
(***************************************************************************)

RequestAction == \E p \in Proc : Request(p) 
EnterAction == \E p \in Proc : Enter(p)
ExitAction == \E p \in Proc : Exit(p)
ReceiveRequestAction == \E p \in Proc : \E q \in Proc \ {p} : ReceiveRequest(p,q)
ReceiveAckAction == \E p \in Proc : \E q \in Proc \ {p} : ReceiveAck(p,q)
ReceiveReleaseAction == \E p \in Proc : \E q \in Proc \ {p} : ReceiveRelease(p,q)

Next ==
    \/ RequestAction
    \/ EnterAction
    \/ ExitAction
    \/ ReceiveRequestAction
    \/ ReceiveAckAction
    \/ ReceiveReleaseAction


vars == <<req, network, clock, ack, crit>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* A state constraint that is useful for validating the specification      *)
(* using finite-state model checking.                                      *)
(***************************************************************************)
ClockConstraint == \A p \in Proc : clock[p] <= maxClock

(***************************************************************************)
(* No channel ever contains more than three messages. In fact, no channel  *)
(* ever contains more than one message of the same type, as proved below.  *)
(***************************************************************************)
BoundedNetwork == \A p,q \in Proc : Len(network[p][q]) <= 3

(***************************************************************************)
(* The main safety property of mutual exclusion.                           *)
(***************************************************************************)
Mutex == \A p,q \in crit : p = q

CTICost == 0
NextUnchanged == UNCHANGED vars


H_Inv36_R0_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
H_Inv306_R1_0_I1_def == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
H_Inv875_R2_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : ~(VARJ \in crit) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
H_Inv840_R3_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
H_Inv695_R3_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
H_Inv381_R4_0_I1_def == \A VARI \in Proc : \A VARJ \in Proc : (beats(VARI,VARJ)) \/ (~(ack[VARI] = {}))
H_Inv92_R5_0_I1_def == \A VARI \in Proc : (VARI \in ack[VARI]) \/ ((ack[VARI] = {}))

HInv19_R0_0_I1 == \A VARI \in Proc : ~(VARI \in crit)

H_Inv565 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))


A_Inv364_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
A_Inv186_R0_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
A_Inv275_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
A_Inv165_R0_0_I1 == \A VARI \in Proc : (\A VOTHER \in Proc \ {VARI} : beats(VARI,VOTHER) /\ req = req) \/ (~(VARI \in crit))
A_Inv1320_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
A_Inv39_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
A_Inv914_R3_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
A_Inv166_R4_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))
A_Inv35_R7_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ crit = crit) \/ (~(network[VARI][VARJ] # <<>>))

IndGlobal1 == 
  /\ Mutex
  /\ A_Inv364_R0_0_I1
  /\ A_Inv1320_R1_0_I1
  /\ A_Inv914_R3_1_I1
  /\ A_Inv35_R7_0_I1
  /\ A_Inv39_R1_1_I1
  /\ A_Inv186_R0_0_I1
  /\ A_Inv275_R0_0_I1
  /\ A_Inv165_R0_0_I1
  /\ A_Inv166_R4_1_I1

B_Inv364_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
B_Inv186_R0_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
B_Inv275_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
B_Inv229_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (beats(VARI,VARJ) /\ req = req) \/ (~(ack[VARI] = {}))
B_Inv1320_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
B_Inv914_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
B_Inv39_R3_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
B_Inv839_R5_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "rel") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
B_Inv549_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARI \in crit))
B_Inv1330_R9_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))

IndGlobal2 == 
    /\ B_Inv364_R0_0_I1
    /\ B_Inv186_R0_0_I1
    /\ B_Inv275_R0_0_I1
    /\ B_Inv229_R0_0_I1
    /\ B_Inv1320_R1_0_I1
    /\ B_Inv914_R1_1_I1
    /\ B_Inv39_R3_1_I1
    /\ B_Inv839_R5_1_I1
    /\ B_Inv549_R6_0_I1
    /\ B_Inv1330_R9_1_I1



P_Inv1250_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack"))
P_Inv124_R0_1_I1 == \A VARI \in Proc : (VARI \in ack[VARI]) \/ ((ack[VARI] = {}))
P_Inv35_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ crit = crit) \/ (~(network[VARI][VARJ] # <<>>))
P_Inv574_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
P_Inv832_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "rel") \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] > Head(network[VARJ][VARI]).clock))
P_Inv553_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (network[VARJ][VARI] # <<>>) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
P_Inv653_R1_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARJ] > 0) \/ (~(network[VARI][VARJ][VARRINDI].type = "ack"))
P_Inv19_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))
P_Inv282_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(ack[VARI] = {}) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
P_Inv259_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack"))
P_Inv549_R4_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (network[VARI][VARJ][VARRINDI].type = "ack") \/ (~(VARI \in crit))
P_Inv938_R5_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(network[VARI][VARJ][VARRINDI].type = "rel") \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] > Head(network[VARJ][VARI]).clock))
P_Inv582_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
P_Inv912_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>>) \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] = Head(network[VARJ][VARI]).clock))
P_Inv263_R10_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : ~(VARI \in ack[VARJ]) \/ (~(network[VARI][VARJ][VARRINDI].type = "ack"))
P_Inv270_R15_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(ack[VARI] = Proc) \/ (~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "req"))
P_Inv2170_R16_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(network[VARJ][VARI] # <<>>)) \/ (~(network[VARI][VARJ] # <<>>))
P_Inv289_R16_0_I2 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (VARI \in ack[VARI]) \/ ((ack[VARI] = Proc) \/ (~(network[VARI][VARJ][VARRINDI].type = "req")))
P_Inv179_R17_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
P_Inv277_R19_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))
P_Inv275_R20_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))






==============================================================================
==============================================================================