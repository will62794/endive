------------------------------- MODULE TwoPhase ----------------------------- 
\* benchmark: tla-twophase
EXTENDS TLC, Naturals, FiniteSets

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
  msgsCommit,
  msgsAbort

vars == <<rmState, tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

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
  /\ msgsCommit \in SUBSET [type : {"Commit"}]
  /\ msgsAbort \in SUBSET [type : {"Abort"}]

ApaTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RM
  /\ msgsPrepared \in SUBSET [type : {"Prepared"}, rm : RM]
  /\ msgsCommit \in SUBSET [type : {"Commit"}]
  /\ msgsAbort \in SUBSET [type : {"Abort"}]


Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgsPrepared = {}
  /\ msgsCommit = {}
  /\ msgsAbort = {}
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
  /\ UNCHANGED <<rmState, tmState, msgsPrepared, msgsCommit, msgsAbort>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgsCommit' = msgsCommit \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared, msgsAbort>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgsAbort' = msgsAbort \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared, msgsPrepared, msgsCommit>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgsPrepared' = msgsPrepared \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared, msgsCommit, msgsAbort>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgsCommit
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgsAbort
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgsPrepared, msgsCommit, msgsAbort>>


TMRcvPreparedAction == TRUE /\ \E rm \in RM : TMRcvPrepared(rm) 
RMPrepareAction == TRUE /\ \E rm \in RM : RMPrepare(rm) 
RMChooseToAbortAction == TRUE /\ \E rm \in RM : RMChooseToAbort(rm)
RMRcvCommitMsgAction == TRUE /\ \E rm \in RM : RMRcvCommitMsg(rm) 
RMRcvAbortMsgAction == TRUE /\ \E rm \in RM : RMRcvAbortMsg(rm)
TMAbortAction == TRUE /\ TMAbort
TMCommitAction == TRUE /\ TMCommit

Next ==
  \/ TMCommitAction 
  \/ TMAbortAction
  \/ TMRcvPreparedAction
  \/ RMPrepareAction
  \/ RMChooseToAbortAction
  \/ RMRcvCommitMsgAction
  \/ RMRcvAbortMsgAction

NextAnnotated ==
    \/ TMAbort
    \/ TMCommit
    \/ \E rm \in RM : TMRcvPrepared(rm) 
    \/ \E rm \in RM : RMPrepare(rm)
    \/ \E rm \in RM : RMChooseToAbort(rm)
    \/ \E rm \in RM : RMRcvCommitMsg(rm)
    \/ \E rm \in RM : RMRcvAbortMsg(rm)

-----------------------------------------------------------------------------

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(RM)

\* 
\* Helper lemmas
\* 

\* START_PROOF

msgsAbortCommit == msgsAbort \cup msgsCommit

H_TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ (rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

H_CommitMsgImpliesNoAbortMsg ==  
    ([type |-> "Commit"] \in msgsCommit) => ~([type |-> "Abort"] \in msgsAbort)

H_CommitMsgImpliesNoRMAborted == 
    \A rmi \in RM : ~([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "aborted"))

H_CommittedRMImpliesCommitMsg == 
    \A rmi \in RM : 
        ([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))

H_CommitMsgImpliesAllPrepared == ([type |-> "Commit"] \in msgsAbortCommit) => (tmPrepared = RM)

H_CommitSentImpliesRMsNotWorking == ([type |-> "Commit"] \in msgsAbortCommit) => \A rmi \in RM : rmState[rmi] \in {"committed", "prepared"}

H_AllPreparedImpliesNoRMsWorking == 
    \A rmi \in RM : 
        (tmPrepared = RM) => ~(rmState[rmi] = "working") 

H_RMSentPrepareImpliesNotWorking == 
    \A rmi \in RM : 
        ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) => (~(rmState[rmi] = "working"))

H_AllPreparedImpliesAllPreparesSent == (tmPrepared = RM) => \A rmj \in RM : ([type |-> "Prepared", rm |-> rmj] \in msgsPrepared)

H_CommitMsgImpliesAllPreparesSent == \A rmi \in RM : ([type |-> "Commit"] \in msgsAbortCommit) => ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) 

H_TMKnowsPrepareImpliesRMSentPrepare == \A rmi \in RM : (tmPrepared = tmPrepared \cup {rmi}) => ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) 

\* H_TMKnowsPrepareImpliesRMPreparedCommittedOrAborted
H_TMKnowsPrepareImpliesRMWorking == \A rmi \in RM : (rmi \in tmPrepared) => rmState[rmi] \in {"prepared", "committed", "aborted"}

H_AbortMsgSentImpliesTMAborted == ([type |-> "Abort"] \in msgsAbortCommit) => tmState = "aborted"

H_RMAbortAfterPrepareImpliesTMAborted == \A rmi \in RM :  ((rmState[rmi] = "aborted") /\ ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared)) => tmState = "aborted"


H_RMCommittedImpliesNoAbortMsg == \A rmi \in RM : (rmState[rmi] = "committed") => ([type |-> "Abort"] \notin msgsAbortCommit)

H_RMCommittedImpliesTMCommitted == \A rmi \in RM : (rmState[rmi] = "committed") => tmState = "committed"
H_RMAbortedImpliesTMAborted == \A rmi \in RM : (rmState[rmi] = "aborted") => tmState = "aborted"

H_RMAbortedAndPreparedImpliesTMAborted == 
    \A rmi \in RM : 
        ( /\ rmState[rmi] = "aborted" 
          /\ ((rmi \in tmPrepared) \/ ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared)) ) => tmState = "aborted"

H_RMAbortedImpliesNoCommitMsg == \A rmi \in RM : (rmState[rmi] = "aborted") => ([type |-> "Commit"] \notin msgsAbortCommit)


H_CommitMsgImpliesTMCommitted == \A rmi \in RM : ([type |-> "Commit"] \in msgsAbortCommit) => tmState = "committed"

H_RMCommittedImpliesNoRMsWorking == 
        \A rmi,rmj \in RM : (rmState[rmi] = "committed") => rmState[rmj] \in {"prepared", "committed"}

H_RMWorkingImpliesNoCommitMsg == 
    \A rmi \in RM : rmState[rmi] = "working" => ([type |-> "Commit"] \notin msgsAbortCommit)

H_RMWorkingImpliesNotPrepared == 
    \A rmi \in RM : rmState[rmi] = "working" => (rmi \notin tmPrepared)

H_InitNoAbortMsg == (tmState = "init") => ~([type |-> "Abort"] \in msgsAbortCommit)
H_InitNoCommitMsg == (tmState = "init") => ~([type |-> "Commit"] \in msgsAbortCommit) 

H_TMAbortedImpliesAbortMsg == \A rmi \in RM : \A rmj \in RM : (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgsAbortCommit))
H_TMCommittedImpliesAbortMsg == \A rmi \in RM : \A rmj \in RM : (tmState = "committed") \/ (~([type |-> "Commit"] \in msgsAbortCommit))

H_AbortMsgImpliesTMAborted == ([type |-> "Abort"] \in msgsAbortCommit) => tmState = "aborted"

H_Inv1863 == \A rmi \in RM : (rmState[rmi] = "prepared") \/ (~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmState = "init")))

H_Inv2000 == \A rmi \in RM : (rmState[rmi] = "prepared") \/ (~(tmPrepared = RM)) \/ (~(tmState = "init"))


H_Inv8880 == \A rmi \in RM : ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))
H_Inv8881 == \A rmi \in RM : (~(rmState[rmi] = "committed")) \/ (~(tmState = "init"))

H_Inv7777 == \A rmi \in RM :  ((rmState[rmi] = "aborted") /\ ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared)) => tmState = "aborted"

H_Inv446 == \A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(rmState[rmi] = "working"))

Inv1433_2_7_def2 == \A rmi \in RM : \A rmj \in RM : (rmState[rmi] = "prepared") \/ (~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared))

Inv89_1_0 == \A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv326_1_1_def == \A rmi \in RM : \A rmj \in RM : (tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgsAbortCommit))
Inv51_1_2_def == \A rmi \in RM : \A rmj \in RM : ([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))
Inv446_1_3_def == \A rmi \in RM : \A rmj \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(rmState[rmi] = "working"))
Inv362_1_4_def == \A rmi \in RM : \A rmj \in RM : (tmState = "aborted") \/ (~([type |-> "Abort"] \in msgsAbortCommit))
Inv380_1_5_def == \A rmi \in RM : \A rmj \in RM : (tmState = "committed") \/ (~([type |-> "Commit"] \in msgsAbortCommit))
Inv479_1_6_def == \A rmi \in RM : \A rmj \in RM : ~(rmState[rmi] = "aborted") \/ (~(tmState = "committed"))
Inv1433_2_7_def == \A rmi \in RM : \A rmj \in RM : (rmState[rmi] = "prepared") \/ (~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmState = "init")))
Inv339_1_0_def == \A rmi \in RM : \A rmj \in RM : (tmPrepared = RM) \/ (~(tmState = "committed"))

Inv89_1_0b == \A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv330_1_1 == \A rmi \in RM : (tmPrepared = RM) \/ (~(rmState[rmi] = "committed"))
Inv429_1_2 == \A rmi \in RM : ~([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "aborted"))
Inv415_1_3 == \A rmi \in RM : ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))
Inv507_1_4 == \A rmi \in RM : ~(rmState[rmi] = "working") \/ (~(tmPrepared = RM))

\* Constant initialization for model checking with Apalache.
CInit == RM = {"1_OF_RM", "2_OF_RM", "3_OF_RM"}

ApaInv == 
    /\ TypeOK 
    /\ H_CommitMsgImpliesNoAbortMsg
    /\ H_CommitMsgImpliesNoRMAborted
    \* /\ H_CommittedRMImpliesCommitMsg
    \* /\ H_CommitMsgImpliesAllPrepared
    \* /\ H_CommitMsgImpliesAllRMsPreparedOrCommitted
    \* /\ H_AllPreparedImpliesNoRMsWorking
    \* /\ H_RMSentPrepareImpliesNotWorking

Safe == H_TCConsistent

\* Dummy CTI cost for now.
CTICost == 
    Cardinality(msgsAbortCommit) + 
    Cardinality(msgsPrepared) + 
    Cardinality(tmPrepared) + 
    \* Consider initial TM states as lower cost.
    IF tmState = "init" THEN 0 ELSE 1

H_Inv13_R0_1_I1_0 == \A VARRMI \in RM : ~(rmState[VARRMI] = "committed")

\* Inv328_R2_0_I1_0_def == ~(tmState = "init") \/ (~([type |-> "Commit"] \in msgsAbortCommit))
\* Inv435_R2_1_I1_0_def == \A VARRMI \in RM : ~(tmPrepared = tmPrepared \cup {VARRMI}) \/ (~(rmState[VARRMI] = "working"))
\* Inv264_R2_1_I1_1_def == \A VARRMI \in RM : ~([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared) \/ (~(rmState[VARRMI] = "working"))
\* Inv450_R2_2_I1_0_def == \A VARRMJ \in RM : ~(tmPrepared = tmPrepared \cup {VARRMJ}) \/ (([type |-> "Prepared", rm |-> VARRMJ] \in msgsPrepared))
\* Inv2408_R2_2_I3_1_def == \A VARRMJ \in RM : (rmState[VARRMJ] = "prepared") \/ (~([type |-> "Prepared", rm |-> VARRMJ] \in msgsPrepared) \/ ~((tmState = "init")))
\* Inv46_R2_3_I1_0_def == ~(tmState = "init") \/ ~(([type |-> "Commit"] \in msgsAbortCommit))
\* 


H_Inv103_R0_0_I1 == \A VARRMI \in RM : \A VARRMJ \in RM : ~(rmState[VARRMI] = "working") \/ (~(rmState[VARRMJ] = "committed"))
H_Inv137_R0_1_I1 == \A VARRMI \in RM : ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~(rmState[VARRMI] = "committed"))
H_Inv135_R1_0_I1 == ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~([type |-> "Commit"] \in msgsAbortCommit))
H_Inv36_R3_0_I1 == ~([type |-> "Commit"] \in msgsAbortCommit) \/ (~(tmState = "init"))
H_Inv90_R3_1_I1 == ~([type |-> "Abort"] \in msgsAbortCommit) \/ (~(tmState = "init"))

=============================================================================