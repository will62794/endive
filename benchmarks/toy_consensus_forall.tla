---- MODULE toy_consensus_forall ----
\* benchmark: pyv-toy-consensus-forall

EXTENDS TLC, Naturals, FiniteSets

CONSTANT Node
CONSTANT Value
CONSTANT Nil

VARIABLE vote
VARIABLE voted
VARIABLE decided

vars == <<vote, voted, decided>>

\* The set of all majority quorums in the Node set.
Quorums == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

\* Node 'i' casts a vote for value 'v'.
CastVote(i, v) == 
    /\ ~voted[i]
    /\ vote' = [vote EXCEPT ![i] = v]
    /\ voted' = [voted EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<decided>>

\* Decide on a value 'v' with quorum 'Q'.
Decide(v, Q) == 
    /\ \A n \in Q : vote[n] = v
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<vote,voted>>

Init ==
    /\ vote = [n \in Node |-> Nil]
    /\ voted = [n \in Node |-> FALSE]
    /\ decided = {}

Next == 
    \/ \E i \in Node, v \in Value : CastVote(i, v)
    \/ \E v \in Value, Q \in Quorums : Decide(v, Q)

NextUnchanged == UNCHANGED vars

\* Can only decide on a single value
Inv == \A vi,vj \in decided : vi = vj

TypeOK == 
    /\ vote \in [Node -> Value \cup {Nil}]
    /\ voted \in [Node -> BOOLEAN]
    /\ decided \in SUBSET Value

Symmetry == Permutations(Node)

\*
\* Weakest precondition.
\*

(**

Inv == \A vi,vj \in decided : vi = vj
wp(Next, Inv) ==
    /\ ENABLED CastVote(i,v) => wp(Post(CastVote), Inv)
    /\ ENABLED Decide(v,Q)   => wp(Post(Decide), Inv)

A1 == wp(Decide, Inv) ==
    /\ \A v \in Value, Q \in Quorum : 
        \A n \in Q : (vote[n] = v) => \A vi,vj \in (decided \cup {v}) : vi = vj

A2 == wp(CastVote, A1) ==
    \A i \in Node, v \in Value :
        ~voted[i] => 
            \A vz \in Value, Q \in Quorum : 
            \A n \in Q : ([vote EXCEPT ![i] = v][n] = vz) => \A vi,vj \in (decided \cup {vz}) : vi = vj

A3 == wp(Decide, A1) ==
    \A v \in Value, Q \in Quorum :
        (\A n \in Q : vote[n] = v) => 
            \A vz \in Value, Q \in Quorum : 
            \A n \in Q : (vote[n] = vz) => \A vi,vj \in ((decided \cup {v}) \cup {vz}) : vi = vj

**)


====