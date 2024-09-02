------------------------------- MODULE Bakery -------------------------------
(***************************************************************************)
(* The bakery algorithm originally appeared in:                            *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* The code for the algorithm given in that paper is :                     *)
(*                                                                      `. *)
(*   begin integer j;                                                      *)
(*   L1: choosing [i] := 1 ;                                               *)
(*       number[i] := 1 + maximum (number[1],..., number[N]);              *)
(*       choosing[i] := 0;                                                 *)
(*       for j = 1 step l until N do                                       *)
(*          begin                                                          *)
(*            L2: if choosing[j] /= 0 then goto L2;                        *)
(*            L3: if number[j] /= 0 and (number [j], j) < (number[i],i)    *)
(*                  then goto L3;                                          *)
(*          end;                                                           *)
(*       critical section;                                                 *)
(*       number[i] := O;                                                   *)
(*       noncritical section;                                              *)
(*       goto L1 ;                                                         *)
(*   end                                                               .'  *)
(*                                                                         *)
(* What makes the bakery algorithm interesting is that it doesn't assume   *)
(* that reading or writing a memory register is an atomic operation.       *)
(* Instead it assumes safe registers, which ensure only that a read that   *)
(* doesn't overlap a write obtains the current value of the register, but  *)
(* allows a read that overlaps a write to obtain any value of the correct  *)
(* type.  This is modeled in TLA+ by letting the read be atomic but having *)
(* a write operation perform a sequence of atomic writes of arbitrary      *)
(* type-correct values before atomically writing the desired value.  (Only *)
(* the shared registers number[i] and choosing[i] need be to be modeled in *)
(* this way; operations to a process's local variables can be taken to be  *)
(* atomic.)                                                                *)
(*                                                                         *)
(* This PlusCal version of the Atomic Bakery algorithm is one in which     *)
(* variables whose initial values are not used are initialized to          *)
(* particular type-correct values.  If the variables were left             *)
(* uninitialized, the PlusCal translation would initialize them to a       *)
(* particular unspecified value.  This would complicate the proof because  *)
(* it would make the type-correctness invariant more complicated, but it   *)
(* would be more efficient to model check.  We could write a version that  *)
(* is more elegant and easy to prove, but less efficient to model check,   *)
(* by initializing the variables to arbitrarily chosen type-correct        *)
(* values.                                                                 *)
(***************************************************************************)
EXTENDS Naturals, TLC, FiniteSets
(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)
CONSTANT N
ASSUME N \in Nat

(***************************************************************************)
(* We define Procs to be the set {1, 2, ...  , N} of processes.            *)
(***************************************************************************)
Procs == 1..N 

(***************************************************************************)
(* \prec is defined to be the lexicographical less-than relation on pairs  *)
(* of numbers.                                                             *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(***       this is a comment containing the PlusCal code *

{ variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1 ;
    { ncs:- while (TRUE) 
            { e1:   either { flag[self] := ~ flag[self] ;
                             goto e1 }
                    or     { flag[self] := TRUE;
                             unchecked := Procs \ {self} ;
                             max := 0
                           } ;     
              e2:   while (unchecked # {}) 
                      { with (i \in unchecked) 
                          { unchecked := unchecked \ {i};
                            if (num[i] > max) { max := num[i] }
                          }
                      };
              e3:   either { with (k \in Nat) { num[self] := k } ;
                             goto e3 }
                    or     { with (i \in {j \in Nat : j > max}) 
                               { num[self] := i }
                           } ;
              e4:   either { flag[self] := ~ flag[self] ;
                             goto e4 }
                    or     { flag[self] := FALSE;
                             unchecked := Procs \ {self} 
                           } ;
              w1:   while (unchecked # {}) 
                      {     with (i \in unchecked) { nxt := i };
                            await ~ flag[nxt];
                        w2: await \/ num[nxt] = 0
                                  \/ <<num[self], self>> \prec <<num[nxt], nxt>> ;
                            unchecked := unchecked \ {nxt};
                      } ;
              cs:   skip ;  \* the critical section;
              exit: either { with (k \in Nat) { num[self] := k } ;
                             goto exit }
                    or     { num[self] := 0 } 
            }
    }
}

***)

VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1a(self) == 
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << num, nxt, unchecked, max >>

e1b(self) == 
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt >>

e2a(self) == 
    /\ pc[self] = "e2"
    /\ unchecked[self] # {}
    /\ \E i \in unchecked[self]:
        /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
        /\ IF num[i] > max[self]
            THEN /\ max' = [max EXCEPT ![self] = num[i]]
            ELSE /\ max' = max
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, flag, nxt >>

e2b(self) == 
    /\ pc[self] = "e2"
    /\ unchecked[self] = {}
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED << num, flag, nxt, unchecked, max >>

e3a(self) == 
    /\ pc[self] = "e3"
    /\ \E k \in Nat: num' = [num EXCEPT ![self] = k]
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

e3b(self) == 
    /\ pc[self] = "e3"
    /\ \E i \in {j \in Nat : j > max[self]}: num' = [num EXCEPT ![self] = i]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

e4a(self) == 
    /\ pc[self] = "e4"
    /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << num, max, nxt, unchecked >>

e4b(self) == 
    /\ pc[self] = "e4"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

w1a(self) == 
    /\ pc[self] = "w1"
    /\ unchecked[self] # {}
    /\ \E i \in unchecked[self]: nxt' = [nxt EXCEPT ![self] = i]
    /\ ~ flag[nxt'[self]]
    /\ pc' = [pc EXCEPT ![self] = "w2"]
    /\ UNCHANGED << num, flag, unchecked, max >>

w1b(self) == 
    /\ pc[self] = "w1"
    /\ (unchecked[self] = {})
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nat:
                         num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) == ncs(self) \/ e1a(self) \/ e1b(self) \/ e2a(self) \/ e2b(self) \/ e3a(self) \/ e3b(self) \/ e4a(self) \/ e4b(self)
              \/ w1a(self) \/ w1b(self) \/ w2(self) \/ cs(self) \/ exit(self)


ncsAction ==  TRUE /\ \E self \in Procs : ncs(self) 
e1aAction ==   TRUE /\ \E self \in Procs : e1a(self) 
e1bAction ==   TRUE /\ \E self \in Procs : e1b(self) 
e2aAction ==   TRUE /\ \E self \in Procs : e2a(self) 
e2bAction ==   TRUE /\ \E self \in Procs : e2b(self) 
e3aAction ==   TRUE /\ \E self \in Procs : e3a(self) 
e3bAction ==   TRUE /\ \E self \in Procs : e3b(self) 
e4aAction ==   TRUE /\ \E self \in Procs : e4a(self)
e4bAction ==   TRUE /\ \E self \in Procs : e4b(self)
w1aAction ==   TRUE /\ \E self \in Procs : w1a(self) 
w1bAction ==   TRUE /\ \E self \in Procs : w1b(self) 
w2Action ==   TRUE /\ \E self \in Procs : w2(self) 
csAction ==   TRUE /\ \E self \in Procs : cs(self) 
exitAction == TRUE /\ \E self \in Procs : exit(self)

Next == 
    \/ ncsAction
    \/ e1aAction
    \/ e1bAction
    \/ e2aAction
    \/ e2bAction
    \/ e3aAction
    \/ e3bAction
    \/ e4aAction
    \/ e4bAction
    \/ w1aAction
    \/ w1bAction
    \/ w2Action
    \/ csAction
    \/ exitAction

\* Spec == /\ Init /\ [][Next]_vars
        \* /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

NextUnchanged == UNCHANGED vars

(***************************************************************************)
(* MutualExclusion asserts that two distinct processes are in their        *)
(* critical sections.                                                      *)
(***************************************************************************)
H_MutualExclusion == \A i,j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Inductive Invariant                                                 *)
(*                                                                         *)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)
TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]             

\* Max(S) == CHOOSE x \in S : \A y \in S : y <= x
\* StateConstraint == \A process \in Procs : num[process] < Max(Nat)

CTICost == 0

H_Inv1145_R0_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "cs"))
H_Inv623_R0_0_I1 == \A VARI \in Procs : (pc[VARI] = "cs") \/ (~(VARI \in unchecked[VARI]))
H_Inv1361_R0_0_I1 == \A VARI \in Procs : ~(flag[VARI]) \/ (~(pc[VARI] = "w1"))
H_Inv1354_R0_0_I1 == \A VARI \in Procs : ~(flag[VARI]) \/ (~(pc[VARI] = "cs"))
H_Inv19_R2_0_I1 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
H_Inv1459_R3_0_I1 == \A VARI \in Procs : ~(flag[VARI]) \/ (~(pc[VARI] = "w2"))

Inv11936_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARI] = "w1")) \/ (~(pc[VARJ] = "cs"))

H_Inv9660_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] = "w1"))


H_Inv20379_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (pc[VARJ] = "e2") \/ ((pc[VARJ] \in {"w1","w2"})) \/ (~(VARI \in unchecked[VARJ]))
H_Inv3134_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>) \/ (~(pc[VARJ] \in {"w1","w2"})) \/ (~(pc[VARI] = "cs"))
H_Inv24963_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(VARI \in (Procs \ unchecked[VARJ])) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "w2")))
H_Inv56_R0_0_I2 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
H_Inv4175_R0_0_I1 == \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] = "cs"))

H_Inv29181 == 
    \A VARI \in Procs : 
    \A VARJ \in Procs : 
        ((pc[VARI] = "cs") /\ ((pc[VARJ] = "w1"))) => (unchecked[VARJ] # {})

H_Inv9040 == 
    \A VARI \in Procs : \A VARJ \in Procs : 
        (pc[VARJ] = "exit") \/ (~(VARI \in (Procs \ unchecked[VARJ])) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))


H_Inv30686 == 
    \A VARI \in Procs : \A VARJ \in Procs : ~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "w1") \/ (~(unchecked[VARJ] = {})))


H_Inv49 == \A VARI \in Procs : ~(VARI \in unchecked[VARI])
H_Inv15793 ==  \A VARJ \in Procs : (pc[VARJ] = "e2") \/ ((pc[VARJ] \in {"w1","w2"})) \/ (~(unchecked[VARJ] = Procs \ {VARJ}))
H_Inv3652 ==  \A VARI \in Procs : ~(pc[VARI] = "w2") \/ (~(unchecked[VARI] = {}))

HInv6155_R0_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : (pc[VARI] = "cs") => ~(((unchecked[VARJ] = {})) /\ ((pc[VARJ] = "w1")))

HInv28910 == \A VARI \in Procs : \A VARJ \in Procs : ~((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1")) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}) \/ (~(unchecked[VARJ] = {})))

H_Inv33341_R1_0_I3 == 
    \A VARI \in Procs : 
    \A VARJ \in Procs : 
        (unchecked[VARI] = Procs \ {VARI}) \/ (~(VARI # VARJ /\ pc = pc)) \/ (~(unchecked[VARJ] = {})) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))))

\* Inv1145_R0_0_I1 == \A VARI \in Procs : (unchecked[VARI] = {}) \/ (~(pc[VARI] = "cs"))
\* Inv1454_R0_0_I1 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(pc[VARI] = "cs"))
\* Inv21195_R4_0_I3 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(unchecked[VARI] = {})) \/ (~(pc[VARI] = "w1"))






H_Inv27766 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] = "e3"))

H_Inv33341 == \A VARI \in Procs : \A VARJ \in Procs : (unchecked[VARI] = Procs \ {VARI}) \/ (~(VARI # VARJ /\ pc = pc)) \/ (~(unchecked[VARJ] = {})) \/ (~(((pc[VARJ] \in {"w1","w2"}) /\ (pc[VARI] = "w1"))))


H_Inv39347 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] = "w2")) \/ (~(pc[VARJ] \in {"e4","w1","w2"})) \/ (~(pc[VARI] = "e3"))


\* Inv34 \A VARI \in Procs : \A VARJ \in Procs : (nxt[VARI] = VARJ) \/ ((unchecked[VARI] = Procs \ {VARI}) \/ (~(pc[VARJ] = "w2"))) \/ (~(pc[VARI] \in {"w1","w2"}))
\* Inv101 \A VARI \in Procs : ~(num[VARI] = 0) \/ (~(pc[VARI] \in {"w1","w2"}))
\* Inv3 \A VARI \in Procs : (<<num[VARI], VARI>> \prec <<num[nxt[VARI]], nxt[VARI]>>) \/ (~((pc[nxt[VARI]] = "w2"))) \/ ((unchecked[VARI] = Procs \ {VARI})) \/ (~(pc[VARI] = "w1"))





H_Inv2488 ==  \A VARI \in Procs : \A VARJ \in Procs : (max[VARI] = num[VARJ]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] = "e3"))

H_Inv9856_R14_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] = "e3"))

H_Inv2036_R13_1_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in (Procs \ unchecked[VARJ]) \ {VARJ}) \/ (~(max[VARI] < num[VARJ])) \/ (~(pc[VARJ] \in {"w1","w2"})) \/ (~(VARI \in (Procs \ unchecked[VARJ]))) \/ (~(pc[VARI] = "e3"))

H_Inv13492_R9_0_I2 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] = "e3"))

H_Inv9080_R7_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (pc[VARJ] = "exit") \/ (~(VARI \in (Procs \ unchecked[VARJ])) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] \in {"e4","w1","w2"})) \/ (~(<<num[VARI],VARI>> \prec <<num[VARJ],VARJ>>))




H_Inv11804 == \A VARI \in Procs : \A VARJ \in Procs : ~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] = "cs")) \/ (~(pc[VARI] = "e3"))

H_Inv3790 == 
    \A VARI \in Procs : 
    \A VARJ \in Procs : 
        (max[VARJ] >= num[VARI]) \/ (~(VARJ \in (Procs \ unchecked[VARI])) \/ (~(pc[VARI] \in {"w1"})) \/ (~(pc[VARJ] = "e3")))

H_Inv3790_B == 
    \A VARI \in Procs : 
    \A VARJ \in Procs : 
        ((pc[VARI] \in {"w2"}) /\ (pc[VARJ] = "e3") /\ (VARJ \notin (unchecked[VARI]))) => (max[VARJ] >= num[VARI])

\* eliminated by support lemma???
Inv1893_R0_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(pc[VARI] = "w2")) \/ ((pc[VARI] = "cs")) \/ ((max[VARJ] >= num[VARI])) \/ (~(pc[VARJ] = "e2")) \/ ((VARJ \in unchecked[VARI]))

H_Inv10852 == \A VARI \in Procs : \A VARJ \in Procs : (max[VARJ] >= num[VARI]) \/ (~(pc[VARI] = "cs") \/ (~(pc[VARJ] = "e3")))


H_Inv3160 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ ((num[VARI] = 1)) \/ (~(pc[VARI] = "e3")) \/ (~(max[VARI] < num[VARJ])) \/ ((pc[VARI] = "ncs")) \/ (~(pc[VARJ] \in {"w1","w2"}))


H_Inv2400_R9_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARJ \in unchecked[VARI]) \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] = "cs"))) \/ (~(pc[VARI] = "e2")) \/ ((pc[VARJ] = "ncs")) \/ ((unchecked[VARI] = Procs))

H_Inv21 == \A VARI \in Procs : (num[VARI] = 0) \/ (~(pc[VARI] = "e2"))
H_Inv5275 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~(pc[VARI] = "w2")) \/ (~((pc[nxt[VARI]] = "e3")))


H_Inv4917 == \A VARI \in Procs : (max[nxt[VARI]] >= num[VARI]) \/ (~((pc[nxt[VARI]] = "e3"))) \/ (~(pc[VARI] = "w2"))




H_Inv7389_R15_0_I3 == \A VARI \in Procs : \A VARJ \in Procs : (max[VARJ] >= num[VARI]) \/ (~(pc[VARJ] = "e3")) \/ (~(pc[VARI] \in {"w1","w2"})) \/ (~(VARJ \in (Procs \ unchecked[VARI]) \ {VARI}))

H_Inv1690_R17_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ ((unchecked[VARI] = Procs \ {VARI}) \/ (~(pc[VARI] = "cs"))) \/ (~(pc[VARJ] = "e2")) \/ ((max[VARJ] >= num[VARI])) \/ (~(VARJ \in Procs \ {VARI}))


H_Inv5163_R0_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[nxt[VARI]]) \/ (~((pc[nxt[VARJ]] = "e2"))) \/ ((max[nxt[VARI]] >= num[VARI])) \/ (~(pc[VARI] = "w2")) \/ ((VARJ \in Procs \ {VARI}))
H_Inv270_R0_1_I1 == \A VARI \in Procs : (flag[VARI]) \/ (~(pc[VARI] = "e3"))
H_Inv12_R1_0_I1 == \A VARJ \in Procs : (flag[VARJ]) \/ (~(pc[VARJ] = "e2"))


H_Inv3258 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARJ] \in {"w1","w2"}))) \/ (~(pc[VARI] = "e3"))

L_Inv3292_R0_0_I4 == \A VARI \in Procs : \A VARJ \in Procs : (VARI \in unchecked[VARJ]) \/ ((pc[VARJ] = "e1") \/ (~(max[VARI] < num[VARJ]) \/ (~(pc[VARI] = "e2"))) \/ (~(unchecked[VARI] = {}))) \/ (~(pc[VARJ] \in {"w1","w2"}))

=============================================================================
\* Modification History
\* Last modified Tue Dec 18 13:48:46 PST 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
