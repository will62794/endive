---- MODULE two_phase_commit ----
\* benchmark: i4-two-phase-commit

EXTENDS TLC

CONSTANT Node

VARIABLE vote_yes
VARIABLE vote_no
VARIABLE alive
VARIABLE go_commit
VARIABLE go_abort
VARIABLE decide_commit
VARIABLE decide_abort

VARIABLE abort_flag

vars == <<vote_yes,vote_no,alive,go_commit,go_abort,decide_commit,decide_abort,abort_flag>>

Vote1(n) ==
    /\ n \in alive
    /\ n \notin vote_no
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_yes' = vote_yes \cup {n}
    /\ UNCHANGED <<vote_no,alive,go_commit,go_abort,decide_commit,decide_abort,abort_flag>>

Vote2(n) ==
    /\ n \in alive
    /\ n \notin vote_yes
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_no' = vote_no \cup {n}
    /\ abort_flag' = TRUE
    /\ decide_abort' = decide_abort \cup {n}
    /\ UNCHANGED <<vote_yes,alive,go_commit,go_abort,decide_commit>>

Fail(n) ==
    /\ n \in alive
    /\ alive' = alive \ {n}
    /\ abort_flag' = TRUE
    /\ UNCHANGED <<vote_yes,vote_no,go_commit,go_abort,decide_commit,decide_abort>>

Go1 ==
    /\ \A n \in Node : n \notin go_commit
    /\ \A n \in Node : n \notin go_abort
    /\ \A n \in Node : n \in vote_yes
    /\ go_commit' = Node
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_abort,decide_commit,decide_abort,abort_flag>>

Go2 ==
    /\ \A n \in Node : n \notin go_commit
    /\ \A n \in Node : n \notin go_abort
    /\ \E n \in Node : (n \in vote_no) \/ (n \notin alive)
    /\ go_abort' = Node
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_commit,decide_commit,decide_abort,abort_flag>>

Commit(n) ==
    /\ n \in alive
    /\ n \in go_commit
    /\ decide_commit' = decide_commit \cup {n}
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_commit,go_abort,decide_abort,abort_flag>>

Abort(n) ==
    /\ n \in alive
    /\ n \in go_abort
    /\ decide_abort' = decide_abort \cup {n}
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_commit,go_abort,decide_commit,abort_flag>>

Next ==
    \/ \E n \in Node : Vote1(n)
    \/ \E n \in Node : Vote2(n)
    \/ \E n \in Node : Fail(n)
    \/ Go1
    \/ Go2
    \/ \E n \in Node : Commit(n)
    \/ \E n \in Node : Abort(n)

Init == 
    /\ vote_yes = {}
    /\ vote_no = {}
    /\ alive = Node
    /\ go_commit = {}
    /\ go_abort = {}
    /\ decide_commit = {}
    /\ decide_abort = {}
    /\ abort_flag = FALSE

NextUnchanged == UNCHANGED vars

TypeOK ==
    /\ vote_yes \in SUBSET Node
    /\ vote_no \in SUBSET Node
    /\ alive \in SUBSET Node
    /\ go_commit \in SUBSET Node
    /\ go_abort \in SUBSET Node
    /\ decide_commit \in SUBSET Node
    /\ decide_abort \in SUBSET Node
    /\ abort_flag \in BOOLEAN 
    
Safety == 
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \notin decide_abort) 
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \in vote_yes)
    /\ \A n,n2 \in Node : (n \in decide_abort) => abort_flag

Symmetry == Permutations(Node)

====