---- MODULE SimpleLog ----
EXTENDS TLC, Sequences, Apalache, Naturals

VARIABLE 
    \* @type: Seq(Int);
    log

TypeOK == 
    /\ log = Gen(3)
    /\ \A i \in DOMAIN log : log[i] \in {1,2,3}

P == \A i \in DOMAIN log : log[i] <= 1

Next == log' = [log EXCEPT ![1] = 2]

====