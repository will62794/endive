-------------------------------- MODULE paxos_epr -------------------------------

\*
\* Specification of Paxos based on the model presented in 
\* the paper 'Paxos Made EPR' (OOPSLA 2017).
\*
\* See two online sources of this model:
\* - https://github.com/secure-foundations/SWISS/blob/348b9c4f9b0b2f124b50c8f420d071f4bc0789b3/benchmarks/paxos_epr_missing1.ivy
\* - https://github.com/wilcoxjay/mypyvy/blob/12a8f5434a25587c56814d090b6ab7fa95851e71/examples/pd/paxos_epr.pyv
\*

EXTENDS Integers, FiniteSets, TLC, Randomization
-----------------------------------------------------------------------------

CONSTANT Value, Node, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Node
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      
Round ==  Nat

None == -1
\* None == CHOOSE v : v \notin Value
  (*************************************************************************)
  (* An unspecified value that is not a ballot number.                     *)
  (*************************************************************************)

VARIABLE one_a \* Round
VARIABLE one_b_max_vote \* Node \X Round \X Round \X Value
VARIABLE one_b \* Node \X Round
VARIABLE left_rnd \* Node \X Round
VARIABLE proposal \* Round \X Value
VARIABLE vote \* Node \X Round \X Value
VARIABLE decision \* Node \X Round \X Value

vars == <<one_a,one_b_max_vote,one_b,left_rnd,proposal,vote,decision>>

(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
\* TypeOK == /\ maxBal \in [Acceptor -> Round \cup {-1}]
\*           /\ maxVBal \in [Acceptor -> Round \cup {-1}]
\*           /\ maxVal \in [Acceptor -> Value \cup {None}]
\*           /\ msgs \subseteq Message


\* NumRandSubsets == 6

\* kNumSubsets == 4
\* nAvgSubsetSize == 3

\* TypeOKRandom == 
\*     /\ maxBal \in RandomSubset(NumRandSubsets, [Acceptor -> Round \cup {-1}])
\*     /\ maxVBal \in RandomSubset(NumRandSubsets, [Acceptor -> Round \cup {-1}])
\*     /\ maxVal \in RandomSubset(NumRandSubsets, [Acceptor -> Value \cup {None}])
\*     /\ msgs \in RandomSetOfSubsets(kNumSubsets, nAvgSubsetSize, Message)


\* Init == /\ maxBal = [a \in Acceptor |-> -1]
\*         /\ maxVBal = [a \in Acceptor |-> -1]
\*         /\ maxVal = [a \in Acceptor |-> None]
\*         /\ msgs = {}

Send1a(b) == 
    /\ one_a' = one_a \cup {b}
    /\ UNCHANGED <<one_b_max_vote,one_b,left_rnd,proposal,vote,decision>>

JoinRound(n, r) ==
    \E maxr \in Round \cup {None}, maxv \in Value : 
        /\ r \in one_a
        /\ <<n,r>> \notin left_rnd
        \* Send the 1b message.
        \* Find maximal vote made by this node in an earlier round.
        /\ \/ (maxr = None /\ \A rx \in Round, vx \in Value : ~((r > rx) /\ <<n,rx,vx>> \in vote))
           \/ /\ maxr # None 
              /\ (r > maxr) /\ <<n,maxr,maxv>> \in vote
              /\ (\A mr \in Round, v \in Value : ((r > mr) /\ <<n,mr,v>> \in vote) => (mr <= maxr))
        /\ one_b_max_vote' = one_b_max_vote \cup {<<n,r,maxr,maxv>>}
        /\ one_b' = one_b \cup {<<n,r>>}
        /\ left_rnd' = left_rnd
        /\ UNCHANGED <<one_a,proposal,vote,decision>>

Propose(r,Q) ==
    \E maxr \in Round \cup {None}, v \in Value : 
        /\ \/ (maxr = None /\ \A n \in Node, mr \in Round, mv \in Value : ~(n \in Q /\ (r > mr) /\ <<n,mr,mv>> \in vote))
           \/ /\ maxr # None
              /\ (\E n \in Node : n \in Q /\ ~(r <= maxr) /\ <<n,maxr,v>> \in vote) 
              /\ (\A n \in Node, mr \in Round, mv \in Value : (n \in Q /\ ~(r <= mr) /\ <<n,maxr,mv>> \in vote) => (mr<=maxr))
        /\ \A mv \in Value : <<r,mv>> \notin proposal
        /\ \A n \in Node : n \in Q => <<n,r>> \in one_b
        /\ proposal' = proposal \cup {<<r,v>>}
        /\ UNCHANGED <<one_a,one_b_max_vote,one_b,left_rnd,vote,decision>>

CastVote(n,v,r) ==
    /\ r # None
    /\ <<n,r>> \notin left_rnd
    /\ <<r,v>> \in proposal
    /\ vote' = vote \cup {<<n,r,v>>}
    /\ UNCHANGED <<one_a,one_b_max_vote,one_b,left_rnd,proposal,decision>>


Decide(n,r,v,Q) ==
    /\ r # None
    /\ \A m \in Node : m \in Q => <<m,r,v>> \in vote
    /\ decision' = decision \cup {<<n,r,v>>}
    /\ UNCHANGED <<one_a,one_b_max_vote,one_b,left_rnd,proposal,vote>>

Init ==
    /\ one_a = {} \* Round
    /\ one_b_max_vote = {} \* Node \X Round \X Round \X Value
    /\ one_b = {} \* Node \X Round
    /\ left_rnd = {} \* Node \X Round
    /\ proposal = {} \* Round \X Value
    /\ vote = {} \* Node \X Round \X Value
    /\ decision = {} \* Node \X Round \X Value

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Next == 
    \/ \E b \in Round : Send1a(b)
    \/ \E n \in Node, r \in Round : JoinRound(n, r)
    \/ \E r \in Round, Q \in Quorum : Propose(r,Q)
    \/ \E n \in Node, v \in Value, r \in Round : CastVote(n,v,r)
    \/ \E n \in Node, v \in Value, r \in Round, Q \in Quorum : Decide(n,v,r,Q)

    \* \/ \E b \in Round : \/ Phase1a(b)
    \*                          \/ \E v \in Value : Phase2a(b, v)
    \*     \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)
\* votes == [a \in Acceptor |->  
\*            {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
\*                                                    /\ mm.acc = a }}]

\* VotedFor(a, b, v) == <<b, v>> \in votes[a]

\* ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

\* chosen == {v \in Value : \E b \in Round : ChosenAt(b, v)}

\* Inv == Cardinality(chosen) <= 1

\* Ind ==
\*     /\ TypeOKRandom
\*     /\ Inv

Symmetry == Permutations(Node) \cup Permutations(Value)

NextUnchanged == UNCHANGED vars

\* conjecture (
\*     decision(N1,R1,V1) &
\*     decision(N2,R2,V2)
\* ) -> V1 = V2
Safety == 
    \A n1,n2 \in Node, r1,r2 \in Round, v1,v2 \in Value : 
        (<<n1,r1,v1>> \in decision /\ <<n2,r2,v2>> \in decision) => v1 = v2

============================================================================