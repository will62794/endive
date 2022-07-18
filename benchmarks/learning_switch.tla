---- MODULE learning_switch ----
\* benchmark: pyv-learning-switch

EXTENDS TLC, Naturals, FiniteSets, Randomization

CONSTANT 
    \* @type: Set(Str);
    Node

VARIABLE 
    \* @type: Set(<<Str, Str, Str>>);
    table,
    \* @type: Set(<<Str, Str, Str, Str>>);
    pending


\* @type: (Str, Str) => Bool;
NewPacket(ps,pd) ==
    /\ pending' = pending \cup {<<ps,pd,ps,ps>>}
    /\ UNCHANGED table

\* @type: (Str, Str, Str, Str, Str) => Bool;
Forward(ps,pd,sw0,sw1,nondet) ==
    /\ <<ps,pd,sw0,sw1>> \in pending
    \* Remove all elements whose first element is not 'nondet',
    \* and also add elements for all d \in Node.
    /\ pending' = 
        {<<psa,pda,sw1a,da>> \in pending : psa = nondet} \cup 
        {<<ps,pd,sw1,d>> : d \in Node}
    /\ table' = IF ( (ps # sw1) /\ (\A w \in Node : w # sw1 => <<ps,sw1,w>> \notin table) )
                THEN  table \cup
                      {<<px,n1,n2>> \in Node \X Node \X Node : 
                            /\ px = ps 
                            /\ (<<ps,n1,sw1>> \in table /\ <<ps,sw0,n2>> \in table) }
                ELSE table

Next == 
    \/ \E ps,pd \in Node : NewPacket(ps,pd)
    \/ \E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet)

Init ==
    /\ table = {<<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2}
    /\ pending = {}

NextUnchanged == UNCHANGED <<table,pending>>

TypeOK == 
    /\ table \in SUBSET (Node \X Node \X Node)
    /\ pending \in SUBSET (Node \X Node \X Node \X Node)

\* invariant [safety] 
\* (forall T, X. table(T,X,X)) & 
\* (forall T, X, Y, Z. table(T,X,Y) & table(T,Y,Z) -> table(T,X,Z)) &
\* (forall T, X, Y. table(T,X,Y) & table(T,Y,X) -> X = Y) & 
\* (forall T, X, Y, Z. table(T,X,Y) & table(T,X,Z) -> table(T,Y,Z) | table(T,Z,Y))
Safety == 
    \* /\ TRUE
    \* /\ TypeOK
    /\ \A t,x \in Node : <<t,x,x>> \in table
    /\ \A t,x,y,z \in Node : (<<t,x,y>> \in table /\ <<t,y,z>> \in table) => (<<t,x,z>> \in table)
    /\ \A t,x,y \in Node : (<<t,x,y>> \in table /\ <<t,y,x>> \in table) => (x = y)
    /\ \A t,x,y,z \in Node : (<<t,x,y>> \in table /\ <<t,x,z>> \in table) => (<<t,y,z>> \in table \/ <<t,z,y>> \in table)
    
    \* Correct strengthening conjuncts.
    \* /\ \A ps,pd,s,d \in Node : (<<ps,pd,s,d>> \in pending /\ ps # s) => <<ps,s,ps>> \in table
    \* /\ \A t,x,y \in Node : (<<t,x,y>> \in table /\ t # y /\ x # y) => <<t,y,t>> \in table

\* #invariant [help_3] pending(PS,PD,S,D) & PS ~= S -> table(PS,S,PS)
\* #invariant [help_4] table(T,X,Y) & T ~= Y & X ~= Y -> table(T,Y,T)

StateConstraint == Cardinality(pending) < 5

Symmetry == Permutations(Node)

Test == Cardinality(pending) < 3

\* RandomSetOfSubsets(k,n,S) equals a pseudo-randomly chosen set of subets of S.
\* That is, each element T of the returned set is a subset of S, and k such choices
\* of T are made when selecting these subsets.
\* The average number of elements in each subset is n.

\* TODO: Figure out proper tuning for this.
TypeOKRandom ==
    /\ table \in RandomSetOfSubsets(80000, RandomElement(16..24), (Node \X Node \X Node))
    /\ pending \in RandomSetOfSubsets(50, 8, (Node \X Node \X Node \X Node))

\* \* A1 == <<s2,s1,s0>> \notin table
\* Test == Cardinality(pending) < 2
\* A2 == Cardinality(table) = 16

====