---- MODULE peterson ----
EXTENDS TLC, Naturals, FiniteSets
\*
\* Specification of Peterson's algorithm in TLA+.
\*

(*
    Summary of the algorithm in pseudocode (i.e. PlusCal).

    variables flag = [i \in {0, 1} |-> FALSE],  turn = 0;
        \* Declares the global variables flag and turn and their initial values;
        \* flag is a 2-element array with initially flag[0] = flag[1] = FALSE.
        process (proc \in {0,1}) {
        \* Declares two processes with identifier self equal to 0 and 1.
        a1: while (TRUE) {
                skip ;  \* the noncritical section
        a2:  flag[self] := TRUE ;
        a3:  turn := 1 - self ;   
        a4:  await (flag[1-self] = FALSE) \/ (turn = self);
        cs:  skip ;  \* the critical section
        a5:  flag[self] := FALSE               }     }     }
*)
        
VARIABLE flag, turn

\* The program counter for each process.
VARIABLE pc

vars == << flag, turn, pc >>

\* The set of processes.
CONSTANT ProcSet

ASSUME Cardinality(ProcSet) = 2

\* Return the other process.
Other(p) == CHOOSE q \in ProcSet : q # p

Init == 
    /\ flag = [i \in ProcSet |-> FALSE]
    /\ turn \in ProcSet
    /\ pc = [self \in ProcSet |-> "a1"]

\*
\* The transitions of the protocol.
\*

a1(self) == /\ pc[self] = "a1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << flag, turn >>

\* A process sets its own flag to TRUE.
a2(self) == /\ pc[self] = "a2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ turn' = turn


\* A process updates 'turn'.
a3(self, other) == /\ pc[self] = "a3"
            /\ self # other
            /\ turn' = other
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ flag' = flag

\* A process enters the critical section.
a4(self, other) == 
    /\ self # other
    /\ pc[self] = "a4"
    /\ (flag[other] = FALSE) \/ (turn = self)
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << flag, turn >>

\* A process exits the critical section.
cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << flag, turn >>

\* A process resets its own flag to FALSE after it left the critical section.
a5(self) == /\ pc[self] = "a5"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ turn' = turn

Next == 
    \E self,other \in ProcSet : 
        \/ a1(self)
        \/ a2(self) 
        \/ a3(self, other) 
        \/ a4(self, other) 
        \/ cs(self) 
        \/ a5(self)

Spec == /\ Init /\ [][Next]_vars

\* The mutual exclusion property i.e. the processes cannot be 
\* inside the critical sectuion at the same time.
Mutex == \A p,q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Symmetry == Permutations(ProcSet)
--------------------------------------------------------

TypeOK == 
    /\ flag \in [ProcSet -> {TRUE, FALSE}]
    /\ turn \in ProcSet
    /\ pc \in [ProcSet -> {"a1","a2","a3","a4","a5","cs"}]    


NextUnchanged == UNCHANGED vars
====
