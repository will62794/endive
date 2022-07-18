---- MODULE lockserv_automaton ----
\* benchmark: ex-lockserv-automaton

EXTENDS TLC

CONSTANT Node

VARIABLE lock_msg
VARIABLE unlock_msg
VARIABLE grant_msg

VARIABLE holds_lock

VARIABLE held

vars == <<lock_msg, unlock_msg, grant_msg, holds_lock, held>>

Lock(n) == 
    /\ lock_msg' = [lock_msg EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<unlock_msg, grant_msg, holds_lock, held>>

Unlock(n) == 
    /\ holds_lock[n]
    /\ holds_lock' = [holds_lock EXCEPT ![n] = FALSE]
    /\ unlock_msg' = [unlock_msg EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<lock_msg, grant_msg, held>>

RecvLock(sender) == 
    /\ lock_msg[sender]
    /\ ~held
    /\ held' = TRUE
    /\ lock_msg' = [lock_msg EXCEPT ![sender] = FALSE]
    /\ grant_msg' = [grant_msg EXCEPT ![sender] = TRUE]
    /\ UNCHANGED <<unlock_msg,holds_lock>>

RecvGrant(n) == 
    /\ grant_msg[n]
    /\ grant_msg' = [grant_msg EXCEPT ![n] = FALSE]
    /\ holds_lock' = [holds_lock EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<lock_msg,unlock_msg,held>>

RecvUnlock(sender) == 
    /\ unlock_msg[sender]
    /\ unlock_msg' = [unlock_msg EXCEPT ![sender] = FALSE]
    /\ held' = FALSE
    /\ UNCHANGED <<lock_msg, grant_msg, holds_lock>>

Next ==
    \/ \E n \in Node : Lock(n)
    \/ \E n \in Node : Unlock(n)
    \/ \E n \in Node : RecvLock(n)
    \/ \E n \in Node : RecvGrant(n)
    \/ \E n \in Node : RecvUnlock(n)

Init == 
    /\ lock_msg = [n \in Node |-> FALSE]
    /\ unlock_msg = [n \in Node |-> FALSE]
    /\ grant_msg = [n \in Node |-> FALSE]
    /\ holds_lock = [n \in Node |-> FALSE]
    /\ held = FALSE

NextUnchanged == UNCHANGED vars

TypeOK == 
    /\ lock_msg \in [Node -> BOOLEAN]
    /\ unlock_msg \in [Node -> BOOLEAN]
    /\ grant_msg \in [Node -> BOOLEAN]
    /\ holds_lock \in [Node -> BOOLEAN]
    /\ held \in BOOLEAN

\* No two clients think they hold the lock simultaneously.
Mutex == \A x,y \in Node : (holds_lock[x] /\ holds_lock[y]) => (x = y)

====