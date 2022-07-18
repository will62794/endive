---- MODULE simple_election ----
\* benchmark: ex-simple-election

EXTENDS TLC

CONSTANT Acceptor
CONSTANT Quorum
CONSTANT Proposer

VARIABLE start
VARIABLE promise
VARIABLE leader

vars == <<start,promise,leader>>

DidNotPromise(a) == \A p \in Proposer : <<a,p>> \notin promise
ChosenAt(Q, p) == \A a \in Q : <<a,p>> \in promise

\*
\* Actions.
\*

Send1a(p) ==
    /\ start' = start \cup {p}
    /\ UNCHANGED <<promise,leader>>

Send1b(a, p) ==
    /\ p \in start
    /\ DidNotPromise(a)
    /\ promise' = promise \cup {<<a,p>>}
    /\ UNCHANGED <<start, leader>>

Decide(p, Q) ==
    /\ ChosenAt(Q, p)
    /\ leader' = leader \cup {p}
    /\ UNCHANGED <<start, promise>>

Next ==
    \/ \E p \in Proposer : Send1a(p)
    \/ \E a \in Acceptor, p \in Proposer : Send1b(a, p)
    \/ \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)

Init ==
    /\ start = {}
    /\ promise = {}
    /\ leader = {}

NextUnchanged == UNCHANGED vars

TypeOK ==
    /\ start \in SUBSET Proposer
    /\ promise \in SUBSET (Acceptor \X Proposer)
    /\ leader \in SUBSET Proposer

Safety == \A pi,pj \in Proposer : (pi \in leader /\ pj \in leader) => (pi = pj)

====