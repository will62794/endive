------------------------------ MODULE Boulanger ----------------------------
(***************************************************************************)
(* This is a PlusCal encoding of the Boulangerie Algorithm of Yoram Moses  *)
(* and Katia Patkin--a variant of the Bakery Algorithm--and a proof that   *)
(* it implements mutual exclusion.  The bakery algorithm appeared in       *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* The PlusCal encoding differs from the Moses-Patkin algorithm in one     *)
(* respect.  To enter the critical section, the PlusCal version examines   *)
(* other processes one at a time--in the while loop at label w1.  The      *)
(* Moses-Patkin algorithm performs those examinations in parallel.         *)
(* Because PlusCal does not allow sub-processes, it would be difficult     *)
(* (but not impossible) to express that algorithm in PlusCal.  It would be *)
(* easy to express their version in TLA+ (for example, by modifying the    *)
(* TLA+ translation of the PlusCal code), and it should be straightforward *)
(* to convert the invariance proof presented here to a proof of the more   *)
(* general version.  I will leave that as an exercise for others.          *)
(*                                                                         *)
(* I started with a PlusCal encoding and invariance proof of the Bakery    *)
(* Algorithm.  The only non-obvious part of that encoding is how it        *)
(* represented the safe registers assumed by the algorithm, which are      *)
(* registers in which reads and writes are not atomic.  A safe register is *)
(* represented by a variable r whose value is written by performing some   *)
(* number of atomic writes of non-deterministically chosen "legal" values  *)
(* to r followed by a single write of the desired value.  A read of the    *)
(* register is performed by a single atomic read of r.  It can be shown    *)
(* that this captures the semantics of a safe register.                    *)
(*                                                                         *)
(* Starting from the PlusCal version of the Bakery Algorithm, it was easy  *)
(* to modify it to the Boulangerie Algorithm (with the simplification      *)
(* described above).  I model checked the algorithm on some small models   *)
(* to convince myself that there were no trivial errors that would be      *)
(* likely to arise from an error in the encoding.  I then modified the     *)
(* invariant by a combination of a bit of thinking and a fair amount of    *)
(* trial and error, finding errors in the invariant by model checking very *)
(* small models.  (I checked it on two processes with chosen numbers       *)
(* restricted to be at most 3.)                                            *)
(*                                                                         *)
(* When checking on a small model revealed no error in the invariant, I    *)
(* checked the proof with TLAPS (the TLA+ proof system).  The high level   *)
(* proof, consisting of steps <1>1 - <1>4, are standard and are the same   *)
(* as for the Bakery Algorithm.  TLAPS checks this simple four-step proof  *)
(* for the Bakery Algorithm with terminal BY proofs that just tell it to   *)
(* use the necessary assumptions and to expand all definitions.  This      *)
(* didn't work for the hard part of the Boulangerie Algorithm--step <1>2   *)
(* that checks inductive invariance.                                       *)
(*                                                                         *)
(* When a proof doesn't go through, one keeps decomposing the proof of the *)
(* steps that aren't proved until one sees what the problem is.  This      *)
(* decomposition is done with little thinking and no typing using the      *)
(* Toolbox's Decompose Proof command.  (The Toolbox is the IDE for the     *)
(* TLA+ tools.) Step <1>2 has the form A /\ B => C, where B is a           *)
(* disjunction, and the Decompose Proof command produces a level-<2> proof *)
(* consisting of subgoals essentially of the form A /\ Bi => C for the     *)
(* disjuncts Bi of B.  Two of those subgoals weren't proved.  I decomposed *)
(* them both for several levels until I saw that in one of them, some step *)
(* wasn't preserving the part of the invariant that asserts                *)
(* type-correctness.  I then quickly found the culprit: a silly error in   *)
(* the type invariant in which I had in one place written the set Proc of  *)
(* process numbers instead of the set Nat of natural numbers.  After       *)
(* correcting that error, only one of the level-<2> subgoals remained      *)
(* unproved: step <2>5.  Using the Decompose Proof command as far as I     *)
(* could on that step, one substep remained unproved.  (I think it was at  *)
(* level <5>.) Looking at what the proof obligations were, the obvious     *)
(* decomposition was a two-way case split, which I did by manually         *)
(* entering another level of subproof.  One of those cases weren't proved, *)
(* so I tried another two-way case split on it.  That worked.  I then made *)
(* that substep to the first step of the (level <3>) proof of <2>5, moving *)
(* its proof with it.  With that additional fact, TLAPS was able to prove  *)
(* <2>5 in one more step (the QED step).                                   *)
(*                                                                         *)
(* The entire proof now is about 70 lines.  I only typed 20 of those 70    *)
(* lines.  The rest either came from the original Bakery Algorithm         *)
(* (8-line) proof or were generated by the Decompose Proof Command.        *)
(*                                                                         *)
(* I don't know how much time I actually spent writing the algorithm and   *)
(* its proof.  Except for the final compaction of the (correct) proof of   *)
(* <2>5, the entire exercise took me two days.  However, most of that was  *)
(* spent tracking down bugs in the Toolbox.  We are in the process of      *)
(* moving the Toolbox to a new version of Eclipse, and there are many bugs *)
(* that must be fixed before it's ready to be released.  I would estimate  *)
(* that it would have taken me less than 4 hours without Toolbox bugs.  I  *)
(* find it remarkable how little thinking the whole thing took.            *)
(*                                                                         *)
(* This whole process was a lot easier than trying to write a convincing   *)
(* hand proof--a proof that I would regard as adequate to justify          *)
(* publication of the proof.                                               *)
(***************************************************************************)

EXTENDS Integers, TLC, FiniteSets

CONSTANT Nats

(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)
CONSTANT N 
ASSUME N \in Nats


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

{ variable num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1, previous = -1 ;
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
                    or     { num[self] := max + 1 } ;
              e4:   either { flag[self] := ~ flag[self] ;
                             goto e4 }
                    or     { flag[self] := FALSE;
                               unchecked := IF num[self] = 1
                                              THEN 1..(self-1)
                                              ELSE Procs \ {self} 
                           } ;
              w1:   while (unchecked # {}) 
                      {     with (i \in unchecked) { nxt := i };
                            await ~ flag[nxt];
                            previous := -1 ;
                        w2: if ( \/ num[nxt] = 0
                                 \/ <<num[self], self>> \prec <<num[nxt], nxt>>
                                 \/  /\ previous # -1 
                                     /\ num[nxt] # previous)
                                { unchecked := unchecked \ {nxt};
                                  if (unchecked = {}) {goto cs}
                                  else {goto w1} 
                                }
                              else { previous := num[nxt] ;
                                     goto w2 }
                                                           
                      } ;
              cs:   skip ;  \* the critical section;
              exit: either { with (k \in Nat) { num[self] := k } ;
                             goto exit }
                    or     { num[self] := 0 } 
            }
    }
}
*************)

\* BEGIN TRANSLATION  (this begins the translation of the PlusCal code)
VARIABLES 
    \* @typeAlias: PROCS = Set(Int);
    \* @type: PROCS -> Int; 
    num
VARIABLE 
    \* @type: PROCS -> Bool;
    flag
VARIABLE 
    \* @type: PROCS -> Str;
    pc
VARIABLE 
    \* @type: PROCS -> Set(PROCS);
    unchecked
VARIABLE 
    \* @type: PROCS -> Int;
    max
VARIABLE 
    \* @type: PROCS -> PROCS;
    nxt
VARIABLE 
    \* @type: PROCS -> PROCS;
    previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ previous = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

e1(self) == 
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED <<unchecked, max>>
    /\ UNCHANGED << num, nxt, previous >>

e1MaxUpdate(self) == 
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt, previous >>

e2(self) == /\ pc[self] = "e2"
            /\ unchecked[self] # {}
            /\ \E i \in unchecked[self]:
                /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                /\ IF num[i] > max[self]
                        THEN /\ max' = [max EXCEPT ![self] = num[i]]
                        ELSE /\ TRUE
                            /\ max' = max
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, flag, nxt, previous >>

e2UncheckedEmpty(self) == 
            /\ pc[self] = "e2"
            /\ unchecked[self] = {}
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt, previous >>

e3(self) == 
    /\ pc[self] = "e3"
    /\ \E k \in Nats : num' = [num EXCEPT ![self] = k]
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e3Max(self) == 
        /\ pc[self] = "e3"
        /\ num' = [num EXCEPT ![self] = max[self] + 1]
        /\ pc' = [pc EXCEPT ![self] = "e4"]
        /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = IF num[self] = 1
                                                                THEN 1..(self-1)
                                                                ELSE Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt, previous >>

w1(self) == 
    /\ pc[self] = "w1"
    /\ unchecked[self] # {}
    /\ \E i \in unchecked[self] : nxt' = [nxt EXCEPT ![self] = i]
    /\ ~flag[nxt'[self]]
    /\ previous' = [previous EXCEPT ![self] = -1]
    /\ pc' = [pc EXCEPT ![self] = "w2"]
    /\ UNCHANGED << num, flag, unchecked, max >>

w1Neg(self) == 
    /\ pc[self] = "w1"
    /\ ~(unchecked[self] # {})
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

w2Cond(self) == 
    \/ num[nxt[self]] = 0
    \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
    \/ /\ previous[self] # -1
       /\ num[nxt[self]] # previous[self]

w2(self) == 
    /\ pc[self] = "w2"
    /\ w2Cond(self)
    /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
    /\ IF unchecked'[self] = {}
        THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, flag, max, nxt, previous >>

w2Prev(self) == 
    /\ pc[self] = "w2"
    /\ ~w2Cond(self)
    /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
    /\ pc' = [pc EXCEPT ![self] = "w2"]
    /\ UNCHANGED << num, flag, max, nxt, unchecked >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nats: num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

ncsAction ==  TRUE /\ \E self \in Procs : ncs(self) 
e1Action ==   TRUE /\ \E self \in Procs : e1(self) 
e1MaxUpdateAction ==   TRUE /\ \E self \in Procs : e1MaxUpdate(self) 
e2Action ==   TRUE /\ \E self \in Procs : e2(self) 
e2UncheckedEmptyAction ==   TRUE /\ \E self \in Procs : e2UncheckedEmpty(self) 
e3Action ==   TRUE /\ \E self \in Procs : e3(self) 
e3MaxAction ==   TRUE /\ \E self \in Procs : e3Max(self) 
e4Action ==   TRUE /\ \E self \in Procs : e4(self)
w1Action ==   TRUE /\ \E self \in Procs : w1(self) 
w1NegAction ==   TRUE /\ \E self \in Procs : w1Neg(self) 
w2Action ==   TRUE /\ \E self \in Procs : w2(self) 
w2PrevAction ==   TRUE /\ \E self \in Procs : w2Prev(self) 
csAction ==   TRUE /\ \E self \in Procs : cs(self) 
exitAction == TRUE /\ \E self \in Procs : exit(self)

Next == 
    \/ ncsAction
    \/ e1Action
    \/ e1MaxUpdateAction
    \/ e2Action
    \/ e2UncheckedEmptyAction
    \/ e3Action
    \/ e3MaxAction
    \/ e4Action
    \/ w1Action
    \/ w1NegAction
    \/ w2Action
    \/ w2PrevAction
    \/ csAction
    \/ exitAction

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))


NextUnchanged == UNCHANGED vars

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
StateConstraint == \A process \in Procs : num[process] < Max(Nats)

(***************************************************************************)
(* MutualExclusion asserts that two distinct processes are in their        *)
(* critical sections.                                                      *)
(***************************************************************************)
H_MutualExclusion == \A i,j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")
-----------------------------------------------------------------------------
(***************************************************************************)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)
TypeOK == /\ num \in [Procs -> Nats]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nats]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]
          /\ previous \in [Procs -> Nats \cup {-1}]             

DebugInv == ~(\E pi \in Procs : pc[pi] = "cs")

(***************************************************************************)
(* Before(i, j) is a condition that implies that num[i] > 0 and, if j is   *)
(* trying to enter its critical section and i does not change num[i], then *)
(* j either has or will choose a value of num[j] for which                 *)
(*                                                                         *)
(*     <<num[i],i>> \prec <<num[j],j>>                                     *)
(*                                                                         *)
(* is true.                                                                *)
(***************************************************************************)
Before(i,j) == /\ num[i] > 0
               /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                  \/ /\ pc[j] = "e2"
                     /\ \/ i \in unchecked[j]
                        \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] = "e3"
                     /\ \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] \in {"e4", "w1", "w2"}
                     /\ <<num[i],i>> \prec <<num[j],j>>
                     /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])
                  \/ /\ num[i] = 1
                     /\ i < j

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)  
Inv == 
    /\ TypeOK 

H_L1 == \A i \in Procs : (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
H_L2 == \A i \in Procs : (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
H_L3 == \A i \in Procs : (pc[i] \in {"e2", "e3"}) => flag[i] 
H_L4 == \A i \in Procs : (pc[i] = "w2") => (nxt[i] # i)
H_L5 == \A i \in Procs : (pc[i] \in {"e2", "w1", "w2"}) => i \notin unchecked[i]
H_L6 == \A i \in Procs : (pc[i] \in {"w1", "w2"}) => \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
H_L7 == \A i \in Procs : 
        (/\ pc[i] = "w2"
         /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
            \/ pc[nxt[i]] = "e3") => max[nxt[i]] >= num[i]
H_L8 == \A i \in Procs : (  /\ pc[i] = "w2"
                            /\ previous[i] # -1 
                            /\ previous[i] # num[nxt[i]]
                            /\ pc[nxt[i]] \in {"e4", "w1", "w2", "cs"}) => Before(i, nxt[i])             
H_L9 == \A i \in Procs : (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)


\* \* Sum the elements in the range of a function.
\* RECURSIVE SumFnRange(_)
\* SumFnRange(f) == IF DOMAIN f = {} THEN 0 ELSE
\*   LET x == CHOOSE x \in DOMAIN f : TRUE
    \* IN f[x] + SumFnRange([k \in (DOMAIN f) \ {x} |-> f[k]])

CTICost == 0
    \* SumFnRange(num) + 
    \* SumFnRange([pi \in Procs |-> Cardinality(unchecked[pi])])
    

H_Inv410_R6_0_I1 == \A VARI \in Procs : ~(nxt[VARI] = VARI) \/ (~(pc[VARI] = "w2"))


=============================================================================
\* Modification History
\* Last modified Tue Aug 27 12:22:38 PDT 2019 by loki
\* Last modified Thu May 24 20:03:58 CEST 2018 by merz
\* Last modified Thu May 24 13:49:22 CEST 2018 by merz
\* Last modified Tue Jul 21 17:55:23 PDT 2015 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
