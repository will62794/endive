-------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC, Randomization
-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in Voting.  *)
(***************************************************************************)
CONSTANT Value, Acceptor

Quorum == {i \in SUBSET(Acceptor) : Cardinality(i) * 2 > Cardinality(Acceptor)}

\* ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                        \*    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      
Ballot ==  Nat

None == CHOOSE v : v \notin Value
  (*************************************************************************)
  (* An unspecified value that is not a ballot number.                     *)
  (*************************************************************************)
  
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.                                        *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]


Message1a ==      [type : {"1a"}, bal : Ballot]
Message1b ==      [type : {"1b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
Message2a ==      [type : {"2a"}, bal : Ballot, val : Value]
Message2b ==      [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

-----------------------------------------------------------------------------
VARIABLE maxBal, 
         maxVBal, \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         msgs1a,     \* The set of all messages that have been sent.
         msgs1b,     \* The set of all messages that have been sent.
         msgs2a,     \* The set of all messages that have been sent.
         msgs2b,     \* The set of all messages that have been sent.
         chosen

(***************************************************************************)
(* NOTE:                                                                   *)
(* The algorithm is easier to understand in terms of the set msgs of all   *)
(* messages that have ever been sent.  A more accurate model would use     *)
(* one or more variables to represent the messages actually in transit,    *)
(* and it would include actions representing message loss and duplication  *)
(* as well as message receipt.                                             *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss because we  *)
(* are mainly concerned with the algorithm's safety property.  The safety  *)
(* part of the spec says only what messages may be received and does not   *)
(* assert that any message actually is received.  Thus, there is no        *)
(* difference between a lost message and one that is never received.  The  *)
(* liveness property of the spec that we check makes it clear what         *)
(* messages must be received (and hence either not lost or successfully    *)
(* retransmitted if lost) to guarantee progress.                           *)
(***************************************************************************)

vars == <<maxBal, maxVBal, maxVal, msgs1a, msgs1b, msgs2a, msgs2b, chosen>>
  (*************************************************************************)
  (* It is convenient to define some identifier to be the tuple of all     *)
  (* variables.  I like to use the identifier `vars'.                      *)
  (*************************************************************************)
  
\* Set of all subsets of a set of size <= k.

(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs1a \in SUBSET Message1a
          /\ msgs1b \in SUBSET Message1b
          /\ msgs2a \in SUBSET Message2a
          /\ msgs2b \in SUBSET Message2b
          /\ chosen \in SUBSET Value


NumRandSubsets == 35

kNumSubsets == 18
nAvgSubsetSize == 4

\* TypeOKRandom == 
\*     /\ maxBal \in RandomSubset(NumRandSubsets, [Acceptor -> Ballot \cup {-1}])
\*     /\ maxVBal \in RandomSubset(NumRandSubsets, [Acceptor -> Ballot \cup {-1}])
\*     /\ maxVal \in RandomSubset(NumRandSubsets, [Acceptor -> Value \cup {None}])
\*     \* /\ msgs \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, Message)


Init == /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVal = [a \in Acceptor |-> None]
        /\ msgs1a = {}
        /\ msgs1b = {}
        /\ msgs2a = {}
        /\ msgs2b = {}
        /\ chosen = {}

(***************************************************************************)
(* The actions.  We begin with the subaction (an action that will be used  *)
(* to define the actions that make up the next-state action.               *)
(***************************************************************************)
Send(m, ms) == ms' = ms \cup {m}

\* Helper predicates for checking presence of message types.
msg1a(a,b) == \E m \in msgs1a : m.type= "1b" /\ m.bal = a
msg1b(a,b,mb,v) == \E m \in msgs1b : m.type= "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = mb /\ m.mval = v
msg2a(b,v) == \E m \in msgs2a : m.type= "2a" /\ m.bal = b /\ m.val = v
msg2b(a,b,v) == \E m \in msgs2b : m.type= "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

(***************************************************************************)
(* In an implementation, there will be a leader process that orchestrates  *)
(* a ballot.  The ballot b leader performs actions Phase1a(b) and          *)
(* Phase2a(b).  The Phase1a(b) action sends a phase 1a message (a message  *)
(* m with m.type = "1a") that begins ballot b.                             *)
(***************************************************************************)
Phase1a(b) == 
    /\ msgs1a' = msgs1a \cup {[type |-> "1a", bal |-> b]}
    /\ UNCHANGED <<maxBal, maxVBal,maxVal,msgs1b,msgs2a,msgs2b,chosen>>
                 

                
(***************************************************************************)
(* Upon receipt of a ballot b phase 1a message, acceptor a can perform a   *)
(* Phase1b(a) action only if b > maxBal[a].  The action sets maxBal[a] to  *)
(* b and sends a phase 1b message to the leader containing the values of   *)
(* maxVBal[a] and maxVal[a].                                               *)
(***************************************************************************)
Phase1b(a) == 
    \E m \in msgs1a : 
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ msgs1b' = msgs1b \cup {[type |-> "1b", acc |-> a, bal |-> m.bal, mbal |-> maxVBal[a], mval |-> maxVal[a]]}
        /\ UNCHANGED <<maxVBal, maxVal,msgs1a,msgs2a,msgs2b,chosen>>

(***************************************************************************)
(* The Phase2a(b, v) action can be performed by the ballot b leader if two *)
(* conditions are satisfied: (i) it has not already performed a phase 2a   *)
(* action for ballot b and (ii) it has received ballot b phase 1b messages *)
(* from some quorum Q from which it can deduce that the value v is safe at *)
(* ballot b.  These enabling conditions are the first two conjuncts in the *)
(* definition of Phase2a(b, v).  This second conjunct, expressing          *)
(* condition (ii), is the heart of the algorithm.  To understand it,       *)
(* observe that the existence of a phase 1b message m in msgs implies that *)
(* m.mbal is the highest ballot number less than m.bal in which acceptor   *)
(* m.acc has or ever will cast a vote, and that m.mval is the value it     *)
(* voted for in that ballot if m.mbal # -1.  It is not hard to deduce from *)
(* this that the second conjunct implies that there exists a quorum Q such *)
(* that ShowsSafeAt(Q, b, v) (where ShowsSafeAt is defined in module       *)
(* Voting).                                                                *)
(*                                                                         *)
(* The action sends a phase 2a message that tells any acceptor a that it   *)
(* can vote for v in ballot b, unless it has already set maxBal[a]         *)
(* greater than b (thereby promising not to vote in ballot b).             *)
(***************************************************************************)
Q1b(Q, b) ==
    {m \in msgs1b : /\ m.type = "1b"
                    /\ m.acc \in Q
                    /\ m.bal = b}

Q1bv(Q, b) == {m \in Q1b(Q,b) : m.mbal \geq 0}
    
Phase2a(b, v) ==
  /\ ~ \E m \in msgs2a : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum :
        /\ \A a \in Q : \E m \in Q1b(Q,b) : m.acc = a 
        /\ \/ Q1bv(Q, b) = {}
           \/ \E m \in Q1bv(Q, b) : 
                /\ m.mval = v
                /\ \A mm \in Q1bv(Q, b) : m.mbal \geq mm.mbal 
  /\ msgs2a' = msgs2a \cup {[type |-> "2a", bal |-> b, val |-> v]}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal,msgs1a,msgs1b,msgs2b,chosen>>
  
(***************************************************************************)
(* The Phase2b(a) action is performed by acceptor a upon receipt of a      *)
(* phase 2a message.  Acceptor a can perform this action only if the       *)
(* message is for a ballot number greater than or equal to maxBal[a].  In  *)
(* that case, the acceptor votes as directed by the phase 2a message,      *)
(* setting maxVBal[a] and maxVal[a] to record that vote and sending a      *)
(* phase 2b message announcing its vote.  It also sets maxBal[a] to the    *)
(* message's.  ballot number                                               *)
(***************************************************************************)
Phase2b(a) == 
    \E m \in msgs2a : 
        /\ m.type = "2a"
        /\ m.bal \geq maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ msgs2b' = msgs2b \cup {[type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val]} 
        /\ UNCHANGED <<msgs1a,msgs1b,msgs2a,chosen>>


votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs2b: /\ mm.type = "2b"
                                                     /\ mm.acc = a }}]
               
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

\* chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Learn(val) == 
    /\ val \in {v \in Value : \E b \in Ballot : ChosenAt(b, v)}
    /\ chosen' = chosen \cup {val}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs1a, msgs1b, msgs2a, msgs2b>>

(***************************************************************************)
(* The actions that can be performed in the next state.                   *)

(***************************************************************************)
(* In an implementation, there will be learner processes that learn from   *)
(* the phase 2b messages if a value has been chosen.  The learners are     *)
(* omitted from this abstract specification of the algorithm.              *)
(***************************************************************************)

Phase1aAction == TRUE /\ \E b \in Ballot : Phase1a(b)
Phase2aAction == TRUE /\ \E b \in Ballot : \E v \in Value : Phase2a(b, v)
Phase1bAction == TRUE /\ \E a \in Acceptor : Phase1b(a) 
Phase2bAction == TRUE /\ \E a \in Acceptor : Phase2b(a)
LearnAction == TRUE /\ \E v \in Value : Learn(v)

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Next == 
    \/ Phase1aAction
    \/ Phase2aAction
    \/ Phase1bAction
    \/ Phase2bAction
    \/ LearnAction

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the refinement mapping under which this algorithm         *)
(* implements the specification in module Voting.                          *)
(***************************************************************************)

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)


DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum : 
      \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
   
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] >= b
  /\ \E c \in -1..(b-1) : 
      /\ (c /= -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

Inv == Cardinality(chosen) <= 1

Ind ==
    /\ TypeOK
    /\ Inv

Symmetry == Permutations(Acceptor) \cup Permutations(Value)

NextUnchanged == UNCHANGED vars

\* K == \A ACCI \in Acceptor : (\E m \in msgs : m.bal >= maxBal[ACCI]) \/ ((maxVBal[ACCI] = -1) /\ (TRUE))

(***************************************************************************)
(* The inductive invariant Inv explains why the Paxos consensus algorithm  *)
(* implements the Voting algorithm.  It is defined after the INSTANCE      *)
(* statement because it uses the operator V!ShowsSafeAt imported by that   *)
(* statement.                                                              *)
(***************************************************************************)


H_L1 == \A a \in Acceptor : maxBal[a] >= maxVBal[a]

H_L2 == \A a \in Acceptor : IF maxVBal[a] = -1
                                THEN maxVal[a] = None
                                ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

H_L3 == \A m \in msgs1b : (m.type = "1b") => /\ maxBal[m.acc] >= m.bal

H_NonEmpty1bMsgImpliesAcceptorVotedInPastBallot == 
    \A m \in msgs1b : 
        (m.mbal >= 0) => <<m.mbal, m.mval>> \in votes[m.acc]

H_ValuesSafeAtBallotIn2a == 
    \A m \in msgs2a : 
    \E Q \in Quorum : 
        ShowsSafeAt(Q, m.bal, m.val)

H_UniqueValuesPerBallotIn2aMsgs == 
    \A mi,mj \in msgs2a : 
        (mj.type ="2a" /\ mj.bal = mi.bal) => mj.val = mi.val

H_L7 == \A m \in msgs2b : (m.type = "2b") => /\ maxVBal[m.acc] >= m.bal

H_ValueAcceptedAtBallotImpliesCorresponding2a == 
    \A m \in msgs2b : 
    \E mm \in msgs2a : 
        /\ mm.type = "2a"
        /\ mm.bal  = m.bal
        /\ mm.val  = m.val

\* 
\* Originally from https://github.com/tlaplus/Examples/blob/master/specifications/PaxosHowToWinATuringAward/Paxos.tla.
\* 
\* IndInv == 
\*  /\ TypeOK
\*  /\ \A a \in Acceptor : maxBal[a] >= maxVBal[a]
\*  /\ \A a \in Acceptor : IF maxVBal[a] = -1
\*                           THEN maxVal[a] = None
\*                           ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]
\*  /\ \A m \in msgs : 
\*        /\ (m.type = "1b") => /\ maxBal[m.acc] >= m.bal
\*                              /\ (m.mbal >= 0) =>  
\*                                  <<m.mbal, m.mval>> \in votes[m.acc]
\*        /\ (m.type = "2a") => /\ \E Q \in Quorum :  ShowsSafeAt(Q, m.bal, m.val)
\*                              /\ \A mm \in msgs : /\ mm.type ="2a"
\*                                                  /\ mm.bal = m.bal
\*                                                  => mm.val = m.val
\*        /\ (m.type = "2b") => /\ maxVBal[m.acc] >= m.bal
\*                              /\ \E mm \in msgs : /\ mm.type = "2a"
\*                                                  /\ mm.bal  = m.bal
\*                                                  /\ mm.val  = m.val

IndInv == 
    /\ H_L1
    /\ H_L2
    /\ H_L3
    /\ H_NonEmpty1bMsgImpliesAcceptorVotedInPastBallot
    /\ H_ValuesSafeAtBallotIn2a
    /\ H_UniqueValuesPerBallotIn2aMsgs
    /\ H_L7
    /\ H_ValueAcceptedAtBallotImpliesCorresponding2a


CTICost == 
    Cardinality(msgs1a) + 
    Cardinality(msgs1b) +
    Cardinality(msgs2a) +
    Cardinality(msgs2b)

============================================================================