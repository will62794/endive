------------------------------- MODULE TwoPhase ----------------------------- 
\* benchmark: tla-twophase
EXTENDS TLC, Naturals

(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)

CONSTANT 
    \* @type: Set(RM);
    RM \* The set of resource managers

\* Message ==
\*   (*************************************************************************)
\*   (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
\*   (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
\*   (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
\*   (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
\*   (* of such a message.                                                    *)
\*   (*************************************************************************)
\*   [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
\*   [type : {"Prepared", "Commit", "Abort"}, rm : RM] 

VARIABLES
  \* @type: RM -> Str;
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  \* @type: Str;
  tmState,       \* The state of the transaction manager.
  \* @type: Set(RM);
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared" messages
  \* @type: Set( { type: Str, rm: RM } );
  msgsPrepared,
  \* @type: Set( { type: Str } );
  msgsAbortCommit

vars == <<rmState, tmState, tmPrepared, msgsPrepared, msgsAbortCommit>>

    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  Since we are specifying only safety, a process is not    *)
    (* required to receive a message, so there is no need to model message *)
    (* loss.  (There's no difference between a process not being able to   *)
    (* receive a message because the message was lost and a process simply *)
    (* ignoring the message.)  We therefore represent message passing with *)
    (* a variable $msgs$ whose value is the set of all messages that have  *)
    (* been sent.  Messages are never removed from $msgs$.  An action      *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the existence of that message in *)
    (* $msgs$.  (Receipt of the same message twice is therefore allowed;   *)
    (* but in this particular protocol, receiving a message for the second *)
    (* time has no effect.)                                                *)
    (***********************************************************************)

TypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgsPrepared \in SUBSET [type : {"Prepared"}, rm : RM]
  /\ msgsAbortCommit \in SUBSET [type : {"Commit", "Abort"}]

Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgsPrepared = {}
  /\ msgsAbortCommit = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgsPrepared
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgsPrepared, msgsAbortCommit>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgsAbortCommit' = msgsAbortCommit \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgsAbortCommit' = msgsAbortCommit \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgsPrepared' = msgsPrepared \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, msgsAbortCommit>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsAbortCommit>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgsAbortCommit
  /\ rmState[rm] # "committed" \* no need to commit twice.
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsAbortCommit>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgsAbortCommit
  /\ rmState[rm] # "aborted" \* no need to abort twice.
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsAbortCommit>>

Next ==
  \/ TMCommit 
  \/ TMAbort
  \/ \E rm \in RM : TMRcvPrepared(rm) 
  \/ \E rm \in RM : RMPrepare(rm) 
  \/ \E rm \in RM : RMChooseToAbort(rm)
  \/ \E rm \in RM : RMRcvCommitMsg(rm) 
  \/ \E rm \in RM : RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
TPSpec == Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgsPrepared, msgsAbortCommit>>

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(RM)

TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ (rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

THEOREM TPSpec => []TypeOK

\* Helper lemmas

\* Level 1.
H_Inv276 == (tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgsAbortCommit))
H_Inv318 == ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~([type |-> "Commit"] \in msgsAbortCommit))
H_Inv334 == \A rmi \in RM : ~([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "aborted"))
H_Inv79 == \A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
H_Inv400 == \A rmi \in RM : ~(rmState[rmi] = "working") \/ (~(tmPrepared = RM))
H_Inv45 == \A rmi \in RM : ([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))

\* Level 2.
H_Inv331 == ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~(tmState = "init"))
H_Inv344 == ~([type |-> "Commit"] \in msgsAbortCommit) \/ (~(tmState = "init"))

\* Level 2.
H_Inv9990 == \A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~([type |-> "Commit"] \in msgsAbortCommit))
H_Inv9991 == \A rmj \in RM : ([type |-> "Prepared", rm |-> rmj] \in msgsPrepared) \/ (~(tmPrepared = RM))

\* Level 3.
H_Inv349 == \A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(rmState[rmi] = "working"))
H_Inv1863 == \A rmi \in RM : (rmState[rmi] = "prepared") \/ (~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmState = "init")))

H_Inv2000 == \A rmi \in RM : (rmState[rmi] = "prepared") \/ (~(tmPrepared = RM)) \/ (~(tmState = "init"))


H_Inv8880 == \A rmi \in RM : ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))
H_Inv8881 == \A rmi \in RM : (~(rmState[rmi] = "committed")) \/ (~(tmState = "init"))

\* If a resource manager has aborted and also prepared, then transaction manager must have decided to abort.
H_Inv7777 == \A rmi \in RM :  ((rmState[rmi] = "aborted") /\ ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared)) => tmState = "aborted"

H_Inv362 == (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgsAbortCommit))
H_Inv446 == \A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(rmState[rmi] = "working"))


\* 
\* Simple/minimal TLAPS proof structure example, just to test hierarchy/folding behavior.
\* 

L1 == 1
L2 == 2
L3 == 3
L4 == 5
L5 == 5

THEOREM TCConsistent
  <1>1. L1
    <2>1. L4
        <3>1. L4 OBVIOUS
        <3>2. L4 OBVIOUS
        <3>3. L4 OBVIOUS
        <3>4. QED OBVIOUS
    <2>2. L5 OBVIOUS
    <2>3. QED OBVIOUS
  <1>2. L2 OBVIOUS
  <1>3. L3 OBVIOUS
  <1>4. L4 OBVIOUS
  <1>5. QED OBVIOUS



\* ApaInv == TypeOK /\ TCConsistent
\* ApaInv == TypeOK /\ H_Inv344
ApaInv == TypeOK /\ H_Inv362 /\ H_Inv446 /\ H_Inv7777
ApaInv2 == 
    /\ TypeOK 
    /\ H_Inv9990
    /\ H_Inv9991
    /\ H_Inv331
    /\ H_Inv2000
    /\ H_Inv334 \* to check in next state

CInit == RM = {"1_OF_RM", "2_OF_RM", "3_OF_RM"}


  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Two-Phase Commit protocol implements the         *)
(* Transaction Commit protocol of module $TCommit$.  The following         *)
(* statement defines $TC!TCSpec$ to be formula $TSpec$ of module           *)
(* $TCommit$.  (The TLA$^+$ \textsc{instance} statement is used to rename  *)
(* the operators defined in module $TCommit$ avoids any name conflicts     *)
(* that might exist with operators in the current module.)                 *)
(***************************************************************************)
\* TC == INSTANCE TCommit 

\* THEOREM TPSpec => TC!TCSpec
  (*************************************************************************)
  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
  (* Commit protocol implements the specification TCSpec of the            *)
  (* Transaction Commit protocol.                                          *)
  (*************************************************************************)
(***************************************************************************)
(* The two theorems in this module have been checked with TLC for six      *)
(* RMs, a configuration with 50816 reachable states, in a little over a    *)
(* minute on a 1 GHz PC.                                                   *)
(***************************************************************************)
=============================================================================