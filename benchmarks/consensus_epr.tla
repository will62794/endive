---- MODULE consensus_epr ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANT 
    \* @type: Set(Str);
    Node,
    \* @type: Set(Str);
    Value

VARIABLE 
    \* @type: Set(<<Str,Str>>);
    vote_request_msg,
    \* @type: Str -> Bool;
    voted,
    \* @type: Set(<<Str,Str>>);
    vote_msg,
    \* @type: Str -> Set(Str);
    votes,
    \* @type: Str -> Bool;
    leader,
    \* @type: Str -> Set(Str);
    decided

vars == <<vote_request_msg,voted,vote_msg,votes,leader,decided>>

Quorum == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

SendRequestVote(src, dst) == 
    /\ vote_request_msg' = vote_request_msg \cup {<<src, dst>> }
    /\ UNCHANGED <<voted,vote_msg,votes,leader,decided>>

\* @type: (Str,Str) => Bool;
SendVote(src, dst) == 
    /\ ~voted[src]
    /\ <<dst,src>> \in vote_request_msg
    /\ vote_msg' = vote_msg \cup {<<src,dst>>}
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    \* Delete vote request message.
    /\ vote_request_msg' = vote_request_msg \ {<<src,dst>>}
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

SendRequestVoteAction == TRUE /\ \E i,j \in Node : SendRequestVote(i,j)
SendVoteAction == TRUE /\ \E i,j \in Node : SendVote(i,j)
RecvVoteAction == TRUE /\ \E i,j \in Node : RecvVote(i,j)
BecomeLeaderAction == TRUE /\ \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
DecideAction == TRUE /\ \E i,j \in Node, v \in Value : Decide(i,v)

Next == 
    \/ SendRequestVoteAction
    \/ SendVoteAction
    \/ RecvVoteAction
    \/ BecomeLeaderAction
    \/ DecideAction

\* Any two chosen values must be consistent.
H_NoConflictingValues == 
    \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)


TypeOK == 
    /\ vote_request_msg \in SUBSET(Node \X Node)
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in SUBSET(Node \X Node)
    /\ votes \in [Node -> SUBSET Node]
    /\ leader \in [Node -> BOOLEAN]
    /\ decided \in [Node -> SUBSET Value]

ApaTypeOK == 
    /\ vote_request_msg \in SUBSET(Node \X Node)
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in SUBSET(Node \X Node)
    /\ votes \in [Node -> SUBSET Node]
    /\ leader \in [Node -> BOOLEAN]
    /\ decided \in [Node -> SUBSET Value]

CInit == 
    /\ Node = {"n1", "n2", "n3", "n4"}
    /\ Value = {"v1", "v2", "v3", "v4"}

SafetyWithTypeOK ==
    /\ TypeOK 
    /\ \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)


NextUnchanged == UNCHANGED vars

\* 
\* Helper lemmas.
\* 

NodesEq(VI, VJ) == VI = VJ /\ votes = votes

\* H_NoConflictingValues == 
\*     \A n1,n2 \in Node, v1,v2 \in Value : 
\*         (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)

H_UniqueLeaders == \A n1,n2 \in Node : leader[n1] /\ leader[n2] => n1 = n2
H_DecidedImpliesLeader == \A n \in Node : decided[n] # {} => leader[n]

H_LeaderHasQuorum == \A n \in Node : leader[n] => \E Q \in Quorum : votes[n] = Q
H_NodesCantVoteTwice == \A n,ni,nj \in Node : ~(ni # nj /\ n \in votes[ni] /\ n \in votes[nj])

H_VoteRecordedImpliesVoteMsg == \A ni,nj \in Node : nj \in votes[ni] => <<nj,ni>> \in vote_msg
H_NodesCantSendVotesToDifferentNodes == \A mi,mj \in vote_msg : (mi[1] = mj[1]) => mi = mj

H_VoteMsgImpliesNodeVoted == \A mi \in vote_msg : voted[mi[1]]


====