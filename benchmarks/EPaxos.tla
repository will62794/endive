-------------------------- MODULE EPaxos --------------------------
\* 
\* Specification of the Egalitarian Paxos protocol.
\* 
\* Original source: https://github.com/efficient/epaxos/tree/master/tla%2B
\* 


EXTENDS Naturals, FiniteSets, TLC, Randomization

(*********************************************************************************)
(* Constant parameters:                                                          *)
(*       Commands: the set of all possible commands                              *)
(*       Replicas: the set of all EPaxos replicas                                *)
(*       FastQuorums(r): the set of all fast quorums where r is a command leader *)
(*       SlowQuorums(r): the set of all slow quorums where r is a command leader *)
(*********************************************************************************)

CONSTANTS Commands, Replicas, MaxBallot

\* CONSTANTS FastQuorums(_), SlowQuorums(_), 

ASSUME IsFiniteSet(Replicas)

(***************************************************************************)
(* Quorum conditions:                                                      *)
(*  (simplified)                                                           *)
(***************************************************************************)

\* ASSUME \A r \in Replicas:
\*   /\ SlowQuorums(r) \subseteq SUBSET Replicas
\*   /\ \A SQ \in SlowQuorums(r): 
\*     /\ r \in SQ
\*     /\ Cardinality(SQ) = (Cardinality(Replicas) \div 2) + 1

\* ASSUME \A r \in Replicas:
\*   /\ FastQuorums(r) \subseteq SUBSET Replicas
\*   /\ \A FQ \in FastQuorums(r):
\*     /\ r \in FQ
\*     /\ Cardinality(FQ) = (Cardinality(Replicas) \div 2) + 
\*                          ((Cardinality(Replicas) \div 2) + 1) \div 2
    
FastQuorums(r) == {a \in SUBSET Replicas: r \in a /\ Cardinality(a) = ((Cardinality(Replicas) \div 2) + ((Cardinality(Replicas) \div 2) + 1) \div 2)}
SlowQuorums(r) == {a \in SUBSET Replicas: r \in a /\ Cardinality(a) = ((Cardinality(Replicas) \div 2) + 1) }

MyMax(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i

(***************************************************************************)
(* Special none command                                                    *)
(***************************************************************************)

CONSTANT none
\* none == CHOOSE c : c \notin Commands

(***************************************************************************)
(* The instance space                                                      *)
(***************************************************************************)

Instances == Replicas \X (1..Cardinality(Commands))

(***************************************************************************)
(* The possible status of a command in the log of a replica.               *)
(***************************************************************************)

Status == {"not-seen", "pre-accepted", "accepted", "committed"}


(*******************************************************************************)
(* Variables:                                                                  *)
(*                                                                             *)
(*          comdLog = the commands log at each replica                         *)
(*          proposed = command that have been proposed                         *)
(*          executed = the log of executed commands at each replica            *)
(*          sentMsg = sent (but not yet received) messages                     *)
(*          crtInst = the next instance available for a command                *)
(*                    leader                                                   *)
(*          leaderOfInst = the set of instances each replica has               *)
(*                         started but not yet finalized                       *)
(*          committed = maps commands to set of commit attributs               *)
(*                      tuples                                                 *)
(*          ballots = largest ballot number used by any                        *)
(*                    replica                                                  *)
(*          preparing = set of instances that each replica is                  *)
(*                      currently preparing (i.e. recovering)                  *) 
(*                                                                             *)
(*                                                                             *)
(*******************************************************************************)

VARIABLES cmdLog, 
          proposed, 
          executed, 
          sentMsg, 
          preAcceptMsg, 
          preAcceptReplyMsg,
          commitMsg,
          acceptMsg,
          acceptReplyMsg,
          prepareMsg,
          prepareReplyMsg,
          tryPreAcceptMsg,
          tryPreAcceptReplyMsg,
          crtInst, 
          leaderOfInst,
          committed, 
          ballots, 
          preparing


(***************************************************************************)
(* All possible protocol messages:                                         *)
(***************************************************************************)


PreAcceptMessage == 
    [type: {"pre-accept"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas,
     cmd: Commands \cup {none}, 
     deps: SUBSET Instances, 
     seq: Nat]

AcceptMessage ==
    [type: {"accept"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas,
     cmd: Commands \cup {none}, 
     deps: SUBSET Instances, 
     seq: Nat]

CommitMessage == 
    [type: {"commit"},
     inst: Instances, 
     ballot: Nat \X Replicas,
     cmd: Commands \cup {none}, 
     deps: SUBSET Instances, 
     seq: Nat]

PrepareMessage ==
    [type: {"prepare"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas]

PreAcceptReplyMessage == 
    [type: {"pre-accept-reply"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas,
     deps: SUBSET Instances, 
     seq: Nat, 
     committed: SUBSET Instances]

AcceptReplyMessage ==
    [type: {"accept-reply"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas]

PrepareReplyMessage ==
    [type: {"prepare-reply"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas, 
     prev_ballot: Nat \X Replicas,
     status: Status,
     cmd: Commands \cup {none}, 
     deps: SUBSET Instances, 
     seq: Nat]    

TryPreAcceptMessage == 
    [type: {"try-pre-accept"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas,
     cmd: Commands \cup {none}, 
     deps: SUBSET Instances, 
     seq: Nat]
                
TryPreAcceptReplyMessage == 
    [type: {"try-pre-accept-reply"}, 
     src: Replicas, 
     dst: Replicas,
     inst: Instances, 
     ballot: Nat \X Replicas, 
     status: Status \cup {"OK"}]

Message ==
    PreAcceptMessage \cup
    AcceptMessage \cup
    CommitMessage \cup
    PrepareMessage \cup
    PreAcceptReplyMessage \cup
    AcceptReplyMessage \cup
    PrepareReplyMessage \cup
    TryPreAcceptMessage \cup
    TryPreAcceptReplyMessage
        
CommandType == 
    [   inst: Instances, 
        status: Status,
        ballot: Nat \X Replicas,
        cmd: Commands \cup {none},
        deps: SUBSET Instances,
        seq: Nat ]

CommittedType == ((Commands \cup {none}) \X (SUBSET Instances) \X Nat)

TypeOK ==
    /\ cmdLog \in [Replicas -> SUBSET CommandType]
    /\ proposed \in SUBSET Commands
    /\ executed \in [Replicas -> SUBSET (Nat \X Commands)]
    /\ sentMsg \in SUBSET Message
    /\ crtInst \in [Replicas -> Nat]
    /\ leaderOfInst \in [Replicas -> SUBSET Instances]
    /\ committed \in [Instances -> SUBSET ((Commands \cup {none}) \X
                                           (SUBSET Instances) \X 
                                           Nat)]
    /\ ballots \in Nat
    /\ preparing \in [Replicas -> SUBSET Instances]
    
\* RandomSetOfSubsets(2, 2, AppendEntriesRequestTypeBounded)

TypeOKRandom == 
    /\ cmdLog \in [Replicas -> RandomSetOfSubsets(2, 2, CommandType)]
    /\ proposed \in SUBSET Commands
    /\ executed \in [Replicas -> SUBSET (Nat \X Commands)]
    /\ sentMsg = {}
    /\ preAcceptMsg \in RandomSetOfSubsets(3,3,PreAcceptMessage)
    /\ preAcceptReplyMsg \in RandomSetOfSubsets(3,3,PreAcceptReplyMessage)
    /\ commitMsg \in RandomSetOfSubsets(3,3,CommitMessage)
    /\ acceptMsg \in RandomSetOfSubsets(3,3,AcceptMessage)
    /\ acceptReplyMsg \in RandomSetOfSubsets(2,2,AcceptReplyMessage)
    /\ prepareMsg \in RandomSetOfSubsets(3,3,PrepareMessage)
    /\ prepareReplyMsg \in RandomSetOfSubsets(3,3,PrepareReplyMessage)
    /\ tryPreAcceptMsg \in RandomSetOfSubsets(3,3,TryPreAcceptMessage)
    /\ tryPreAcceptReplyMsg \in RandomSetOfSubsets(3,3,TryPreAcceptReplyMessage)
    /\ crtInst \in [Replicas -> Nat]
    /\ leaderOfInst \in [Replicas -> SUBSET Instances]
    /\ committed \in [Instances -> RandomSetOfSubsets(3, 3, CommittedType)]
    /\ ballots \in Nat
    /\ preparing \in [Replicas -> SUBSET Instances]    

vars == << cmdLog, proposed, executed, sentMsg, crtInst, leaderOfInst, committed, ballots, preparing >>

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)

Init ==
  /\ sentMsg = {}
  /\ preAcceptMsg = {}
  /\ preAcceptReplyMsg = {}
  /\ commitMsg = {}
  /\ acceptMsg = {}
  /\ acceptReplyMsg = {}
  /\ prepareMsg = {}
  /\ prepareReplyMsg = {}
  /\ tryPreAcceptMsg = {}
  /\ tryPreAcceptReplyMsg = {}
  /\ cmdLog = [r \in Replicas |-> {}]
  /\ proposed = {}
  /\ executed = [r \in Replicas |-> {}]
  /\ crtInst = [r \in Replicas |-> 1]
  /\ leaderOfInst = [r \in Replicas |-> {}]
  \* /\ committed = [i \in Instances |-> {}]
  \* Force concrete evaluation to make TLC happy here for some reason.
  /\ committed = TLCEval([i \in Instances |-> {}]) 
  /\ ballots = 1
  /\ preparing = [r \in Replicas |-> {}]



(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

StartPhase1(C, cleader, Q, inst, ballot, oldMsg) ==
    LET newDeps == {rec.inst: rec \in cmdLog[cleader]} 
        newSeq == 1 + MyMax({t.seq: t \in cmdLog[cleader]}) 
        oldRecs == {rec \in cmdLog[cleader] : rec.inst = inst} IN
        /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ oldRecs) \cup 
                                {[inst   |-> inst,
                                  status |-> "pre-accepted",
                                  ballot |-> ballot,
                                  cmd    |-> C,
                                  deps   |-> newDeps,
                                  seq    |-> newSeq ]}]
        /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {inst}]
        \* /\ sentMsg' = (sentMsg \ oldMsg) \cup 
        /\ preAcceptMsg' = (preAcceptMsg \ oldMsg) \cup 
                                [type  : {"pre-accept"},
                                  src   : {cleader},
                                  dst   : Q \ {cleader},
                                  inst  : {inst},
                                  ballot: {ballot},
                                  cmd   : {C},
                                  deps  : {newDeps},
                                  seq   : {newSeq}]
        /\ UNCHANGED <<sentMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg>>

Propose(C, cleader, Q) ==
    LET newInst == <<cleader, crtInst[cleader]>> 
        newBallot == <<0, cleader>> 
    IN  /\ Q \in FastQuorums(cleader)
        /\ proposed' = proposed \cup {C}
        /\ StartPhase1(C, cleader, Q, newInst, newBallot, {})
        /\ crtInst' = [crtInst EXCEPT ![cleader] = @ + 1]
        /\ UNCHANGED << executed, committed, ballots, preparing >>


Phase1Reply(replica) ==
    \E msg \in preAcceptMsg:
        /\ msg.type = "pre-accept"
        /\ msg.dst = replica
        /\ LET oldRec == {rec \in cmdLog[replica]: rec.inst = msg.inst} IN
            /\ (\A rec \in oldRec : 
                (rec.ballot = msg.ballot \/rec.ballot[1] < msg.ballot[1]))
            /\ LET newDeps == msg.deps \cup 
                            ({t.inst: t \in cmdLog[replica]} \ {msg.inst})
                   newSeq == MyMax({msg.seq, 
                                  1 + MyMax({t.seq: t \in cmdLog[replica]})})
                   instCom == {t.inst: t \in {tt \in cmdLog[replica] :
                              tt.status \in {"committed", "executed"}}} IN
                /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                    {[inst   |-> msg.inst,
                                      status |-> "pre-accepted",
                                      ballot |-> msg.ballot,
                                      cmd    |-> msg.cmd,
                                      deps   |-> newDeps,
                                      seq    |-> newSeq]}]
                /\ preAcceptMsg' = (preAcceptMsg \ {msg})
                /\ preAcceptReplyMsg' = preAcceptReplyMsg \cup
                                    {[type  |-> "pre-accept-reply",
                                      src   |-> replica,
                                      dst   |-> msg.src,
                                      inst  |-> msg.inst,
                                      ballot|-> msg.ballot,
                                      deps  |-> newDeps,
                                      seq   |-> newSeq,
                                      committed|-> instCom]}
                /\ UNCHANGED << sentMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, crtInst, executed, leaderOfInst, committed, ballots, preparing >>

Phase1Fast(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in FastQuorums(cleader)
    /\ \E record \in cmdLog[cleader]:
        /\ record.inst = i
        /\ record.status = "pre-accepted"
        /\ record.ballot[1] = 0
        /\ LET replies == {msg \in preAcceptReplyMsg: 
                                /\ msg.inst = i
                                /\ msg.type = "pre-accept-reply"
                                /\ msg.dst = cleader
                                /\ msg.src \in Q
                                /\ msg.ballot = record.ballot} IN
            /\ (\A replica \in (Q \ {cleader}): 
                    \E msg \in replies: msg.src = replica)
            /\ (\A r1, r2 \in replies:
                /\ r1.deps = r2.deps
                /\ r1.seq = r2.seq)
            /\ LET r == CHOOSE r \in replies : TRUE IN
                /\ LET localCom == {t.inst: 
                            t \in {tt \in cmdLog[cleader] : 
                                 tt.status \in {"committed", "executed"}}}
                       extCom == UNION {msg.committed: msg \in replies} IN
                       (r.deps \subseteq (localCom \cup extCom))    
                /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup 
                                        {[inst   |-> i,
                                          status |-> "committed",
                                          ballot |-> record.ballot,
                                          cmd    |-> record.cmd,
                                          deps   |-> r.deps,
                                          seq    |-> r.seq ]}]
                /\ preAcceptReplyMsg' = preAcceptReplyMsg \ replies
                /\ commitMsg' = commitMsg \cup
                            {[type  |-> "commit",
                            inst    |-> i,
                            ballot  |-> record.ballot,
                            cmd     |-> record.cmd,
                            deps    |-> r.deps,
                            seq     |-> r.seq]}
                /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
                /\ committed' = [committed EXCEPT ![i] = 
                                            @ \cup {<<record.cmd, r.deps, r.seq>>}]
                /\ UNCHANGED << sentMsg,preAcceptMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, ballots, preparing >>

Phase1Slow(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in SlowQuorums(cleader)
    /\ \E record \in cmdLog[cleader]:
        /\ record.inst = i
        /\ record.status = "pre-accepted"
        /\ LET replies == {msg \in preAcceptReplyMsg: 
                                /\ msg.inst = i 
                                /\ msg.type = "pre-accept-reply" 
                                /\ msg.dst = cleader 
                                /\ msg.src \in Q
                                /\ msg.ballot = record.ballot} IN
            /\ (\A replica \in (Q \ {cleader}): \E msg \in replies: msg.src = replica)
            /\ LET finalDeps == UNION {msg.deps : msg \in replies}
                   finalSeq == MyMax({msg.seq : msg \in replies}) IN    
                /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup 
                                        {[inst   |-> i,
                                          status |-> "accepted",
                                          ballot |-> record.ballot,
                                          cmd    |-> record.cmd,
                                          deps   |-> finalDeps,
                                          seq    |-> finalSeq ]}]
                /\ \E SQ \in SlowQuorums(cleader):
                    /\ preAcceptReplyMsg' = preAcceptReplyMsg \ replies
                    /\ acceptMsg' = acceptMsg \cup
                            [type : {"accept"},
                            src : {cleader},
                            dst : SQ \ {cleader},
                            inst : {i},
                            ballot: {record.ballot},
                            cmd : {record.cmd},
                            deps : {finalDeps},
                            seq : {finalSeq}]
                /\ UNCHANGED << sentMsg,preAcceptMsg,commitMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, leaderOfInst, committed, ballots, preparing >>
                
Phase2Reply(replica) ==
    \E msg \in acceptMsg: 
        /\ msg.type = "accept"
        /\ msg.dst = replica
        /\ LET oldRec == {rec \in cmdLog[replica]: rec.inst = msg.inst} IN
            /\ (\A rec \in oldRec: (rec.ballot = msg.ballot \/ 
                                    rec.ballot[1] < msg.ballot[1]))
            /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                {[inst   |-> msg.inst,
                                  status |-> "accepted",
                                  ballot |-> msg.ballot,
                                  cmd    |-> msg.cmd,
                                  deps   |-> msg.deps,
                                  seq    |-> msg.seq]}]
            /\ acceptMsg' = acceptMsg \ {msg}
            /\ acceptReplyMsg' = acceptReplyMsg \cup
                                    {[type  |-> "accept-reply",
                                    src   |-> replica,
                                    dst   |-> msg.src,
                                    inst  |-> msg.inst,
                                    ballot|-> msg.ballot]}
            /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, crtInst, executed, leaderOfInst, committed, ballots, preparing >>


Phase2Finalize(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in SlowQuorums(cleader)
    /\ \E record \in cmdLog[cleader]:
        /\ record.inst = i
        /\ record.status = "accepted"
        /\ LET replies == {msg \in acceptReplyMsg: 
                                /\ msg.inst = i 
                                /\ msg.type = "accept-reply" 
                                /\ msg.dst = cleader 
                                /\ msg.src \in Q 
                                /\ msg.ballot = record.ballot} IN
            /\ (\A replica \in (Q \ {cleader}): \E msg \in replies: 
                                                        msg.src = replica)
            /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup 
                                    {[inst   |-> i,
                                      status |-> "committed",
                                      ballot |-> record.ballot,
                                      cmd    |-> record.cmd,
                                      deps   |-> record.deps,
                                      seq    |-> record.seq ]}]
            /\ acceptReplyMsg' = acceptReplyMsg \ replies
            /\ commitMsg' = commitMsg \cup
                                {[type  |-> "commit",
                                inst    |-> i,
                                ballot  |-> record.ballot,
                                cmd     |-> record.cmd,
                                deps    |-> record.deps,
                                seq     |-> record.seq]}
            /\ committed' = [committed EXCEPT ![i] = @ \cup {<<record.cmd, record.deps, record.seq>>}]
            /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
            /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,acceptMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, ballots, preparing >>

Commit(replica, cmsg) ==
    LET oldRec == {rec \in cmdLog[replica] : rec.inst = cmsg.inst} IN
        /\ \A rec \in oldRec : (rec.status \notin {"committed", "executed"} /\ 
                                rec.ballot[1] <= cmsg.ballot[1])
        /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup 
                                    {[inst     |-> cmsg.inst,
                                      status   |-> "committed",
                                      ballot   |-> cmsg.ballot,
                                      cmd      |-> cmsg.cmd,
                                      deps     |-> cmsg.deps,
                                      seq      |-> cmsg.seq]}]
        /\ committed' = [committed EXCEPT ![cmsg.inst] = @ \cup 
                               {<<cmsg.cmd, cmsg.deps, cmsg.seq>>}]
        /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, leaderOfInst, sentMsg, ballots, preparing >>


(***************************************************************************)
(* Recovery actions                                                        *)
(***************************************************************************)

SendPrepare(replica, i, Q) ==
    /\ i \notin leaderOfInst[replica]
    /\ Q \in SlowQuorums(replica)
    \* This condition states that the instance has been started by its original owner.
    /\ crtInst[i[1]] > i[2] 
    \*/\ i \notin preparing[replica]
    /\ ballots <= MaxBallot
    /\ ~(\E rec \in cmdLog[replica] :
                        /\ rec.inst = i
                        /\ rec.status \in {"committed", "executed"})
    /\ prepareMsg' = prepareMsg \cup
                    [type   : {"prepare"},
                     src    : {replica},
                     dst    : Q,
                     inst   : {i},
                     ballot : {<< ballots, replica >>}]
    /\ ballots' = ballots + 1
    /\ preparing' = [preparing EXCEPT ![replica] = @ \cup {i}]
    /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, cmdLog, proposed, executed, crtInst, leaderOfInst, committed >>
    
ReplyPrepare(replica, msg) ==
        /\ msg.type = "prepare"
        /\ msg.dst = replica
        /\ \/ \E rec \in cmdLog[replica] : 
                /\ rec.inst = msg.inst
                /\ msg.ballot[1] > rec.ballot[1]
                /\ prepareMsg' = prepareMsg \ {msg}
                /\ prepareReplyMsg' = prepareReplyMsg \cup
                            {[type  |-> "prepare-reply",
                              src   |-> replica,
                              dst   |-> msg.src,
                              inst  |-> rec.inst,
                              ballot|-> msg.ballot,
                              prev_ballot|-> rec.ballot,
                              status|-> rec.status,
                              cmd   |-> rec.cmd,
                              deps  |-> rec.deps,
                              seq   |-> rec.seq]}
                 /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
                            {[inst  |-> rec.inst,
                              status|-> rec.status,
                              ballot|-> msg.ballot,  \* problematic use of single variable from Sutra's bug?
                              cmd   |-> rec.cmd,
                              deps  |-> rec.deps,
                              seq   |-> rec.seq]}]
                 /\ IF rec.inst \in leaderOfInst[replica] THEN
                        /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = 
                                                                @ \ {rec.inst}]
                        /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, committed, crtInst, ballots, preparing >>
                    ELSE UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, committed, crtInst, ballots, preparing, leaderOfInst >>
                        
           \/ /\ ~(\E rec \in cmdLog[replica] : rec.inst = msg.inst)
              /\ prepareMsg' = prepareMsg \ {msg}
              /\ prepareReplyMsg' = prepareReplyMsg \cup
                            {[type  |-> "prepare-reply",
                              src   |-> replica,
                              dst   |-> msg.src,
                              inst  |-> msg.inst,
                              ballot|-> msg.ballot,
                              prev_ballot|-> << 0, replica >>,
                              status|-> "not-seen",
                              cmd   |-> none,
                              deps  |-> {},
                              seq   |-> 0]}
              /\ cmdLog' = [cmdLog EXCEPT ![replica] = @ \cup
                            {[inst  |-> msg.inst,
                              status|-> "not-seen",
                              ballot|-> msg.ballot, \* problematic use of single variable from Sutra's bug?
                              cmd   |-> none,
                              deps  |-> {},
                              seq   |-> 0]}]
              /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, committed, crtInst, ballots,leaderOfInst, preparing >> 
    
PrepareFinalize(replica, i, Q) ==
    /\ i \in preparing[replica]
    /\ Q \in SlowQuorums(replica)
    /\ \E rec \in cmdLog[replica] :
       /\ rec.inst = i
       /\ rec.status \notin {"committed", "executed"}
       /\ LET replies == {msg \in prepareReplyMsg : 
                        /\ msg.inst = i
                        /\ msg.type = "prepare-reply"
                        /\ msg.dst = replica
                        /\ msg.ballot = rec.ballot} IN
            /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
            /\  \/ \E com \in replies :
                        /\ (com.status \in {"committed", "executed"})
                        /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                        /\ prepareReplyMsg' = prepareReplyMsg \ replies
                        /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, cmdLog, proposed, executed, crtInst, leaderOfInst, committed, ballots >>
                \/ /\ ~(\E msg \in replies : msg.status \in {"committed", "executed"})
                   /\ \E acc \in replies :
                        /\ acc.status = "accepted"
                        /\ (\A msg \in (replies \ {acc}) : 
                            (msg.prev_ballot[1] <= acc.prev_ballot[1] \/ 
                             msg.status # "accepted"))
                        /\ prepareReplyMsg' = prepareReplyMsg \ replies
                        /\ acceptMsg' = acceptMsg \cup
                                 [type  : {"accept"},
                                  src   : {replica},
                                  dst   : Q \ {replica},
                                  inst  : {i},
                                  ballot: {rec.ballot},
                                  cmd   : {acc.cmd},
                                  deps  : {acc.deps},
                                  seq   : {acc.seq}]
                        /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
                                {[inst  |-> i,
                                  status|-> "accepted",
                                  ballot|-> rec.ballot,
                                  cmd   |-> acc.cmd,
                                  deps  |-> acc.deps,
                                  seq   |-> acc.seq]}]
                         /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                         /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                         /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptReplyMsg,prepareMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, committed, ballots >>
                \/ /\ ~(\E msg \in replies : msg.status \in {"accepted", "committed", "executed"})
                   /\ LET preaccepts == {msg \in replies : msg.status = "pre-accepted"} IN
                       (\/  /\ \A p1, p2 \in preaccepts :
                                    p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
                            /\ ~(\E pl \in preaccepts : pl.src = i[1])
                            /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
                            /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
                                /\ prepareReplyMsg' = prepareReplyMsg \ replies
                                /\ acceptMsg' = acceptMsg \cup
                                         [type  : {"accept"},
                                          src   : {replica},
                                          dst   : Q \ {replica},
                                          inst  : {i},
                                          ballot: {rec.ballot},
                                          cmd   : {pac.cmd},
                                          deps  : {pac.deps},
                                          seq   : {pac.seq}]
                                /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
                                        {[inst  |-> i,
                                          status|-> "accepted",
                                          ballot|-> rec.ballot,
                                          cmd   |-> pac.cmd,
                                          deps  |-> pac.deps,
                                          seq   |-> pac.seq]}]
                                 /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                 /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                 /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptReplyMsg,prepareMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, committed, ballots >>
                        \/  /\ \A p1, p2 \in preaccepts : p1.cmd = p2.cmd /\ 
                                                          p1.deps = p2.deps /\
                                                          p1.seq = p2.seq
                            /\ ~(\E pl \in preaccepts : pl.src = i[1])
                            /\ Cardinality(preaccepts) < Cardinality(Q) - 1
                            /\ Cardinality(preaccepts) >= Cardinality(Q) \div 2
                            /\ LET pac == CHOOSE pac \in preaccepts : TRUE IN
                                /\ prepareReplyMsg' = prepareReplyMsg \ replies
                                /\ tryPreAcceptMsg' = tryPreAcceptMsg \cup
                                         [type  : {"try-pre-accept"},
                                          src   : {replica},
                                          dst   : Q,
                                          inst  : {i},
                                          ballot: {rec.ballot},
                                          cmd   : {pac.cmd},
                                          deps  : {pac.deps},
                                          seq   : {pac.seq}]
                                /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,tryPreAcceptReplyMsg, cmdLog, proposed, executed, crtInst, committed, ballots >>
                        \/  /\ \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/ 
                                                             p1.deps # p2.deps \/
                                                             p1.seq # p2.seq
                               \/ \E pl \in preaccepts : pl.src = i[1]
                               \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
                            /\ preaccepts # {}
                            /\ \E pac \in preaccepts : pac.cmd # none \* added by Will S (10/23/23)
                            /\ LET pac == CHOOSE pac \in preaccepts : pac.cmd # none IN
                                /\ StartPhase1(pac.cmd, replica, Q, i, rec.ballot, replies)
                                /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                /\ UNCHANGED << sentMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg, proposed, executed, crtInst, committed, ballots >>)
                \/  /\ \A msg \in replies : msg.status = "not-seen"
                    /\ StartPhase1(none, replica, Q, i, rec.ballot, replies)
                    /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                    /\ UNCHANGED << proposed, executed, crtInst, committed, ballots >>
                    
ReplyTryPreaccept(replica) ==
    \E tpa \in tryPreAcceptMsg :
        /\ tpa.type = "try-pre-accept" 
        /\ tpa.dst = replica
        /\ LET oldRec == {rec \in cmdLog[replica] : rec.inst = tpa.inst} IN
            /\ \A rec \in oldRec : rec.ballot[1] <= tpa.ballot[1] /\ 
                                   rec.status \notin {"accepted", "committed", "executed"}
            /\ \/ (\E rec \in cmdLog[replica] \ oldRec:
                        /\ tpa.inst \notin rec.deps
                        /\ \/ rec.inst \notin tpa.deps
                           \/ rec.seq >= tpa.seq
                        /\ tryPreAcceptMsg' = tryPreAcceptMsg \ {tpa}
                        /\ tryPreAcceptReplyMsg' = tryPreAcceptReplyMsg \cup
                                    {[type  |-> "try-pre-accept-reply",
                                      src   |-> replica,
                                      dst   |-> tpa.src,
                                      inst  |-> tpa.inst,
                                      ballot|-> tpa.ballot,
                                      status|-> rec.status]})
                        /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg, cmdLog, proposed, executed, committed, crtInst, ballots, leaderOfInst, preparing >>
               \/ /\ (\A rec \in cmdLog[replica] \ oldRec: 
                            tpa.inst \in rec.deps \/ (rec.inst \in tpa.deps /\
                                                      rec.seq < tpa.seq))
                  /\ tryPreAcceptMsg' = tryPreAcceptMsg \ {tpa}
                  /\ tryPreAcceptReplyMsg' = tryPreAcceptReplyMsg \cup
                                    {[type  |-> "try-pre-accept-reply",
                                      src   |-> replica,
                                      dst   |-> tpa.src,
                                      inst  |-> tpa.inst,
                                      ballot|-> tpa.ballot,
                                      status|-> "OK"]}
                  /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                    {[inst  |-> tpa.inst,
                                      status|-> "pre-accepted",
                                      ballot|-> tpa.ballot,
                                      cmd   |-> tpa.cmd,
                                      deps  |-> tpa.deps,
                                      seq   |-> tpa.seq]}]
                  /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg, proposed, executed, committed, crtInst, ballots, leaderOfInst, preparing >>
                      
             
FinalizeTryPreAccept(cleader, i, Q) ==
    \E rec \in cmdLog[cleader]:
        /\ rec.inst = i
        /\ LET tprs == {msg \in tryPreAcceptReplyMsg : msg.type = "try-pre-accept-reply" /\
                            msg.dst = cleader /\ msg.inst = i /\
                            msg.ballot = rec.ballot} IN
            /\ \A r \in Q: \E tpr \in tprs : tpr.src = r
            /\ \/ /\ \A tpr \in tprs: tpr.status = "OK"
                  /\ tryPreAcceptReplyMsg' = tryPreAcceptReplyMsg \ tprs
                  /\ acceptMsg' = acceptMsg \cup
                             [type  : {"accept"},
                              src   : {cleader},
                              dst   : Q \ {cleader},
                              inst  : {i},
                              ballot: {rec.ballot},
                              cmd   : {rec.cmd},
                              deps  : {rec.deps},
                              seq   : {rec.seq}]
                  /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {rec}) \cup
                            {[inst  |-> i,
                              status|-> "accepted",
                              ballot|-> rec.ballot,
                              cmd   |-> rec.cmd,
                              deps  |-> rec.deps,
                              seq   |-> rec.seq]}]
                  /\ UNCHANGED << sentMsg, proposed, executed, committed, crtInst, ballots, leaderOfInst, preparing >>
               \/ /\ \E tpr \in tprs: tpr.status \in {"accepted", "committed", "executed"}
                  /\ StartPhase1(rec.cmd, cleader, Q, i, rec.ballot, tprs)
                  /\ UNCHANGED << sentMsg,preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg, proposed, executed, committed, crtInst, ballots, leaderOfInst, preparing >>
               \/ /\ \E tpr \in tprs: tpr.status = "pre-accepted"
                  /\ \A tpr \in tprs: tpr.status \in {"OK", "pre-accepted"}
                  /\ tryPreAcceptReplyMsg' = tryPreAcceptReplyMsg \ tprs
                  /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
                  /\ UNCHANGED <<preAcceptMsg,preAcceptReplyMsg,commitMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg, sentMsg, cmdLog, proposed, executed, committed, crtInst, ballots, preparing >>
         


(***************************************************************************)
(* Action groups                                                           *)
(***************************************************************************)        

\* CommandLeaderAction ==
\*     \/ (\E C \in (Commands \ proposed) :
\*             \E cleader \in Replicas : Propose(C, cleader))
\*     \/ (\E cleader \in Replicas : \E inst \in leaderOfInst[cleader] :
\*             \/ (\E Q \in FastQuorums(cleader) : Phase1Fast(cleader, inst, Q))
\*             \/ (\E Q \in SlowQuorums(cleader) : Phase1Slow(cleader, inst, Q))
\*             \/ (\E Q \in SlowQuorums(cleader) : Phase2Finalize(cleader, inst, Q))
\*             \/ (\E Q \in SlowQuorums(cleader) : FinalizeTryPreAccept(cleader, inst, Q)))
            
\* ReplicaAction ==
\*     \E replica \in Replicas :
\*         (\/ Phase1Reply(replica)
\*          \/ Phase2Reply(replica)
\*          \/ \E cmsg \in sentMsg : (cmsg.type = "commit" /\ Commit(replica, cmsg))
\*          \/ \E i \in Instances : 
\*             /\ crtInst[i[1]] > i[2] (* This condition states that the instance has *) 
\*                                     (* been started by its original owner          *)
\*             /\ \E Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
\*          \/ ReplyPrepare(replica)
\*          \/ \E i \in preparing[replica] :
\*             \E Q \in SlowQuorums(replica) : PrepareFinalize(replica, i, Q)
\*          \/ ReplyTryPreaccept(replica))


(***************************************************************************)
(* Next action                                                             *)
(***************************************************************************)


ProposeAction == TRUE /\ \E C \in (Commands \ proposed) : \E cleader \in Replicas : \E Q \in FastQuorums(cleader) : Propose(C, cleader, Q)
Phase1FastAction ==  TRUE /\ \E cleader \in Replicas : \E inst \in leaderOfInst[cleader] : \E Q \in FastQuorums(cleader) : Phase1Fast(cleader, inst, Q)
Phase1SlowAction == TRUE /\ \E cleader \in Replicas : \E inst \in leaderOfInst[cleader] : \E Q \in SlowQuorums(cleader) : Phase1Slow(cleader, inst, Q)
Phase2FinalizeAction == TRUE /\ \E cleader \in Replicas : \E inst \in leaderOfInst[cleader] : \E Q \in SlowQuorums(cleader) : Phase2Finalize(cleader, inst, Q)
FinalizeTryPreAcceptAction == TRUE /\ \E cleader \in Replicas : \E inst \in leaderOfInst[cleader] : \E Q \in SlowQuorums(cleader) : FinalizeTryPreAccept(cleader, inst, Q)
Phase1ReplyAction == TRUE /\ \E replica \in Replicas : Phase1Reply(replica)
Phase2ReplyAction == TRUE /\ \E replica \in Replicas : Phase2Reply(replica)
CommitAction == TRUE /\ \E replica \in Replicas : \E cmsg \in sentMsg : (cmsg.type = "commit" /\ Commit(replica, cmsg))
SendPrepareAction == TRUE /\ \E replica \in Replicas : \E i \in Instances : 
    \* This condition states that the instance has been started by its original owner.
    /\ crtInst[i[1]] > i[2] 
    /\ \E Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
ReplyPrepareAction == TRUE /\ \E replica \in Replicas : \E msg \in prepareMsg : ReplyPrepare(replica, msg)
PrepareFinalizeAction == TRUE /\ \E replica \in Replicas : \E i \in preparing[replica] : \E Q \in SlowQuorums(replica) : PrepareFinalize(replica, i, Q)
ReplyTryPreacceptAction == TRUE /\ \E replica \in Replicas : ReplyTryPreaccept(replica)

Next ==
    \/ ProposeAction
    \/ Phase1FastAction
    \/ Phase1SlowAction
    \/ Phase2FinalizeAction
    \/ FinalizeTryPreAcceptAction
    \/ Phase1ReplyAction
    \/ Phase2ReplyAction
    \/ CommitAction
    \/ SendPrepareAction
    \/ ReplyPrepareAction
    \/ PrepareFinalizeAction
    \/ ReplyTryPreacceptAction

NextForAnnotations == 
    \/ \E C \in (Commands \ proposed), cleader \in Replicas, Q \in SUBSET Replicas : Propose(C, cleader, Q)
    \/ \E cleader \in Replicas, inst \in Instances, Q \in SUBSET Replicas : Phase1Fast(cleader, inst, Q)
    \/ \E cleader \in Replicas, inst \in Instances, Q \in SUBSET Replicas : Phase1Slow(cleader, inst, Q)
    \/ \E cleader \in Replicas, inst \in Instances, Q \in SUBSET Replicas : Phase2Finalize(cleader, inst, Q)
    \/ \E cleader \in Replicas : \E inst \in leaderOfInst[cleader] : \E Q \in SlowQuorums(cleader) : FinalizeTryPreAccept(cleader, inst, Q)
    \/ \E replica \in Replicas : Phase1Reply(replica)
    \/ \E replica \in Replicas : Phase2Reply(replica)
    \/ \E replica \in Replicas : \E cmsg \in sentMsg : (cmsg.type = "commit" /\ Commit(replica, cmsg))
    \/ \E replica \in Replicas, i \in Instances, Q \in SUBSET Replicas : SendPrepare(replica, i, Q)
    \/ \E replica \in Replicas, msg \in prepareMsg : ReplyPrepare(replica, msg)
    \/ \E replica \in Replicas : \E i \in preparing[replica] : \E Q \in SUBSET Replicas : PrepareFinalize(replica, i, Q)
    \/ \E replica \in Replicas : ReplyTryPreaccept(replica)

(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars


(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

Nontriviality ==
    \A i \in Instances :
        [](\A C \in committed[i] : C \in proposed \/ C = none)

Stability ==
    \A replica \in Replicas :
        \A i \in Instances :
            \A C \in Commands :
                []((\E rec1 \in cmdLog[replica] :
                    /\ rec1.inst = i
                    /\ rec1.cmd = C
                    /\ rec1.status \in {"committed", "executed"}) =>
                    [](\E rec2 \in cmdLog[replica] :
                        /\ rec2.inst = i
                        /\ rec2.cmd = C
                        /\ rec2.status \in {"committed", "executed"}))

H_Consistency ==
    \A i \in Instances : Cardinality(committed[i]) <= 1

\* Ignores 'none' command.
H_Consistency_Alt ==
    \A i \in Instances : Cardinality({c \in committed[i] : c[1] # none}) <= 1

\* Debug invariant.
Inv1 == ~(\E i \in Instances : Cardinality(committed[i]) = 1)

Symmetry == Permutations(Replicas)

NextUnchanged == UNCHANGED <<cmdLog, proposed, executed, sentMsg, preAcceptMsg, preAcceptReplyMsg,commitMsg,acceptMsg,acceptReplyMsg,prepareMsg,prepareReplyMsg,tryPreAcceptMsg,tryPreAcceptReplyMsg,crtInst, leaderOfInst,committed, ballots, preparing>>

CTICost == 0

=============================================================================
\* Modification History
\* Last modified Sat Aug 24 12:25:28 EDT 2013 by iulian
\* Created Tue Apr 30 11:49:57 EDT 2013 by iulian