---------------------- MODULE ind3cycle ----------------------
EXTENDS Naturals

VARIABLE a,b,c
Init == a = 1 /\ b = 0 /\ c = 0

A == a > 0 /\ b' = a /\ a' = 0 /\ c'=c
B == b > 0 /\ c' = b /\ b' = 0 /\ a'=a
C == c > 0 /\ a' = c /\ c' = 0 /\ b'=b

Next == 
  \/ A 
  \/ B
  \/ C


Inv == a \in {0,1} \* top-level invariant.

L1  == b \in {0,1}
L2  == c \in {0,1}
==============================================================