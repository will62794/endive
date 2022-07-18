---- MODULE consensus_wo_decide ----
\* benchmark: pyv-consensus-wo-decide

EXTENDS TLC, Randomization

CONSTANT Node
CONSTANT Quorums

VARIABLE vote_request_msg
VARIABLE voted
VARIABLE vote_msg
VARIABLE votes
VARIABLE leader
VARIABLE voting_quorum

\* mutable relation vote_request_msg(node, node)
\* mutable relation voted(node)
\* mutable relation vote_msg(node, node)
\* mutable relation votes(node, node)
\* mutable relation leader(node)
\* mutable constant voting_quorum: quorum


\* transition send_request_vote(src: node, dst: node)
\* transition send_vote(src: node, dst: node)
\* transition recv_vote(n: node, sender: node)
\* transition choose_voting_quorum(q, sn)
\* transition become_leader(n: node)

SendRequestVote(i,j) == 
    /\ vote_request_msg' = [vote_request_msg EXCEPT ![<<i,j>>] = TRUE]
    /\ UNCHANGED <<voted, vote_msg, votes, leader, voting_quorum>>

SendVote(src,dst)==
    /\ ~voted[src]
    /\ vote_request_msg[<<dst,src>>]
    /\ vote_msg' = [vote_msg EXCEPT ![<<src,dst>>] = TRUE]
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ UNCHANGED <<vote_request_msg, votes, leader, voting_quorum>>

RecvVote(i,sender)==
    /\ vote_msg[<<sender,i>>]
    /\ votes' = [votes EXCEPT ![<<i,sender>>] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, leader, voting_quorum>>

ChooseVotingQuorum(i) ==
    \E Q \in Quorums :
    /\ \A v \in Q : votes[<<i,v>>]
    /\ voting_quorum' = Q
    /\ UNCHANGED <<vote_request_msg, vote_msg, votes, voted, leader>>

BecomeLeader(i) == 
    /\ voting_quorum # {}
    /\ \A v \in voting_quorum : votes[<<i,v>>]
    /\ leader' = [leader EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, voting_quorum>>

Init == 
    /\ vote_request_msg = [s \in Node \X Node |-> FALSE]
    /\ voted = [s \in Node |-> FALSE]
    /\ vote_msg = [s \in Node \X Node |-> FALSE]
    /\ votes = [s \in Node \X Node |-> FALSE]
    /\ leader = [s \in Node |-> FALSE]
    /\ voting_quorum \in Quorums

Next == 
    \/ \E i,j \in Node : SendRequestVote(i,j)
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node : ChooseVotingQuorum(i)
    \/ \E i \in Node : BecomeLeader(i)

TypeOK == 
    /\ vote_request_msg \in [Node \X Node -> BOOLEAN]
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in [Node \X Node -> BOOLEAN]
    /\ votes \in [Node \X Node -> BOOLEAN]
    /\ leader \in [Node -> BOOLEAN]
    /\ voting_quorum \in Quorums

TypeOKRandom ==
    /\ vote_request_msg \in RandomSubset(25, [Node \X Node -> BOOLEAN])
    /\ voted \in RandomSubset(6, [Node -> BOOLEAN])
    /\ vote_msg \in RandomSubset(25, [Node \X Node -> BOOLEAN])
    /\ votes \in RandomSubset(25, [Node \X Node -> BOOLEAN])
    /\ leader \in RandomSubset(6, [Node -> BOOLEAN])
    /\ voting_quorum \in RandomSubset(4, Quorums)

Safety == \A i,j \in Node : (leader[i] /\ leader[j]) => (i = j)

NoLeader == ~\E i \in Node : leader[i]

Symmetry == Permutations(Node)

NextUnchanged == UNCHANGED <<vote_request_msg,voted,vote_msg,votes,leader,voting_quorum>>

\*
\* Inductive invariant definition.
\*

\* invariant votes(N, N1) -> vote_msg(N1, N)
A1 == \A n,n1 \in Node : votes[<<n,n1>>] => vote_msg[<<n1,n>>]

\* invariant vote_msg(N, N1) & vote_msg(N, N2) -> N1 = N2
A2 == 
    \A n,n1,n2 \in Node : 
        vote_msg[<<n,n1>>] /\ vote_msg[<<n,n2>>] => n1=n2

\* vote_msg(N, N1) -> voted(N)
A3 == \A n,n1 \in Node : vote_msg[<<n,n1>>] => voted[n]

\* invariant leader(N) & member(N1, voting_quorum) -> votes(N, N1)
A4 == \A n,n1 \in Node: (leader[n] /\ n1 \in voting_quorum) => votes[<<n,n1>>]

\* The human generated invariant.
IndHuman == 
    /\ Safety
    /\ A1
    /\ A2
    /\ A3
    /\ A4

Ind == 
    /\ Safety

IInit ==
    /\ TypeOKRandom
    /\ Ind

====