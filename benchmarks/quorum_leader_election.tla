---- MODULE quorum_leader_election ----
\* benchmark: ex-quorum-leader-election

EXTENDS TLC, Naturals, FiniteSets

CONSTANT Node
CONSTANT Nil

VARIABLE isleader
VARIABLE voted

vars == <<isleader, voted>>

\* The set of all majority quorums in the Node set.
Quorums == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

\* Node i casts a vote for node j. Can only vote if it has not already.
Vote(i,j) == 
    /\ voted[i] = Nil
    /\ voted' = [voted EXCEPT ![i]=j]
    /\ UNCHANGED isleader

\* Node i becomes leader with the votes of a quorum Q.
BecomeLeader(i,Q) == 
    \* All nodes in the quorum must have voted for 'i'.
    /\ \A v \in Q : voted[v] = i
    /\ isleader' = [isleader EXCEPT ![i] = TRUE]
    /\ UNCHANGED voted

Init == 
    /\ isleader = [n \in Node |-> FALSE]
    /\ voted = [n \in Node |-> Nil]

Next ==
    \/ \E i,j \in Node : Vote(i,j) 
    \/ \E i \in Node : \E Q \in Quorums : BecomeLeader(i, Q)

\* No more than a single leader can be elected.
Inv == \A i,j \in Node : (isleader[i] /\ isleader[j]) => (i=j)

TypeOK ==
    /\ isleader \in [Node -> BOOLEAN]
    /\ voted \in [Node -> Node \cup {Nil}]

NextUnchanged == UNCHANGED vars

====