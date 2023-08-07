---- MODULE counter ----
EXTENDS TLC, Naturals

VARIABLE x

Init == x = 0

Next == x'=x+1

Constraint == x < 3
Inv == x < 3
====