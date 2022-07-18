---- MODULE consensus_epr ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, Randomization

CONSTANT 
    \* @type: Set(Str);
    Node,
    \* @type: Set(Str);
    Quorum,
    \* @type: Set(Str);
    Value


VARIABLE 
    \* @type: Set(<<Str,Str>>);
    vote_request_msg,
    \* @type: Str -> Str;
    voted,
    \* @type: Set(<<Str,Str>>)
    vote_msg,
    \* @type: Str -> Set(Str)
    votes,
    \* @type: Str -> Bool
    leader,
    \* @type: Str -> Set(Str)
    decided

vars == <<vote_request_msg,voted,vote_msg,votes,leader,decided>>

SendRequestVote(src, dst) == 
    /\ vote_request_msg' = vote_request_msg \cup {<<src, dst>> }
    /\ UNCHANGED <<voted,vote_msg,votes,leader,decided>>

SendVote(src, dst) == 
    /\ ~voted[src]
    /\ <<dst,src>> \in vote_request_msg
    /\ vote_msg' = vote_msg \cup {<<src,dst>>}
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ \/ vote_request_msg' = vote_request_msg \cup {<<src,dst>>}
       \/ vote_request_msg' = vote_request_msg \ {<<src,dst>>}
    /\ UNCHANGED <<votes, leader, decided>>

RecvVote(n, sender) == 
    /\ <<sender,n>> \in vote_msg
    /\ votes' = [votes EXCEPT ![n] = votes[n] \cup {sender}]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,leader,decided>>

BecomeLeader(n, Q) == 
    /\ Q \subseteq votes[n]
    /\ leader' = [leader EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,votes,decided>>

Decide(n, v) == 
    /\ leader[n]
    /\ decided[n] = {}
    /\ decided' = [decided EXCEPT ![n] = decided[n] \cup {v}]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,votes,leader>>

Init == 
    /\ vote_request_msg = {}
    /\ voted = [i \in Node |-> FALSE]
    /\ vote_msg = {}
    /\ votes = [i \in Node |-> {}]
    /\ leader = [i \in Node |-> FALSE]
    /\ decided = [i \in Node |-> {}]

Next == 
    \/ \E i,j \in Node : SendRequestVote(i,j)
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
    \/ \E i,j \in Node, v \in Value : Decide(i,v)

Symmetry == Permutations(Node) \cup Permutations(Value)

TypeOK == 
    /\ vote_request_msg \in SUBSET(Node \X Node)
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in SUBSET(Node \X Node)
    /\ votes \in [Node -> SUBSET Node]
    /\ leader \in [Node -> BOOLEAN]
    /\ decided \in [Node -> SUBSET Value]

TypeOKRandom ==
    /\ vote_request_msg \in RandomSubset(40, SUBSET (Node \X Node)) 
    /\ voted \in RandomSubset(7, [Node -> BOOLEAN])
    /\ vote_msg \in RandomSubset(40, SUBSET(Node \X Node)) 
    /\ votes \in RandomSubset(10, [Node -> SUBSET Node]) 
    /\ leader \in RandomSubset(4, [Node -> BOOLEAN])
    /\ decided \in RandomSubset(10, [Node -> SUBSET Value]) 

\* TypeOKRandom ==
\*     /\ vote_request_msg \in RandomSubset(80, SUBSET (Node \X Node)) 
\*     /\ voted \in RandomSubset(7, [Node -> BOOLEAN])
\*     /\ vote_msg \in RandomSubset(80, SUBSET(Node \X Node)) 
\*     /\ votes \in RandomSubset(10, [Node -> SUBSET Node]) 
\*     /\ leader \in RandomSubset(4, [Node -> BOOLEAN])
\*     /\ decided \in RandomSubset(15, [Node -> SUBSET Value]) 

    \* \A VARI \in Node : \A VARK \in Node : (<<VARI,VARK>> \in vote_msg) \/ (~(VARI \in votes[VARK]))
    \* \A VARI \in Node : \A VALI \in Value : (leader[VARI]) \/ (~(VALI \in decided[VARI]))
    \* \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(VARI \in votes[VARJ]))
    \* \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARJ = VARK /\ votes = votes) \/ (~(<<VARI,VARK>> \in vote_msg)) \/ (~(VARI \in votes[VARJ]))
    \* \E QJ \in Quorum : \A VARJ \in Node : \A VALI \in Value : ~(VALI \in decided[VARJ]) \/ (~(VARJ \in QJ /\ votes = votes))
    \* \A VARI \in Node : \A VARJ \in Node : (<<VARJ,VARI>> \in vote_msg) \/ (~(<<VARI,VARJ>> \in vote_msg) \/ (~(leader[VARI])))
    \* \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARI = VARJ /\ votes = votes) \/ (~(VARK \in votes[VARJ])) \/ (~(VARK \in votes[VARI]))
    \* \E QJ \in Quorum : \A VARI \in Node : ~(VARI \in QJ /\ votes = votes) \/ (~(leader[VARI]))
    \* \A BBBVARI \in Node : \A BBBVARK \in Node : (<<BBBVARI,BBBVARK>> \in vote_msg) \/ (~(BBBVARI \in votes[BBBVARK]))
    \* \E QJ \in Quorum : \A VARI \in Node : ~(VARI \in QJ /\ votes = votes) \/ (~(leader[VARI]))

Safety ==
    \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)

SafetyWithTypeOK ==
    /\ TypeOK 
    /\ \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)


NextUnchanged == UNCHANGED vars
====