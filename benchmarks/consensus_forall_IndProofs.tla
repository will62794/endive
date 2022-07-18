---- MODULE consensus_forall_IndProofs ----
EXTENDS consensus_forall, FiniteSetTheorems, TLAPS

\* endive.py stats
\* -----------------
\* date: 2022-08-03T23:42:05.671399
\* is_inductive: True
\* inv_size: 8
\* invcheck_duration_secs: 81.4364697933197
\* ctielimcheck_duration_secs: 29.43027687072754
\* ctigen_duration_secs: 70.94698214530945
\* total_duration_secs: 181.9267919063568
\* total_num_ctis_eliminated: 10609
\* total_num_cti_elimination_rounds: 2
\* total_num_invs_generated: 975
\* total_num_invs_checked: 18726
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 13
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv358_1_0_def == \A VARI \in Node : \A VARJ \in Node : (<<VARJ,VARI>> \in vote_msg) \/ (~(<<VARI,VARJ>> \in votes))
Inv119_1_1_def == \A VARI \in Node : \A VARJ \in Node : (<<VARI,VARJ>> \in vote_request_msg) \/ (~(<<VARJ,VARI>> \in vote_msg))
Inv759_1_2_def == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(<<VARI,VARJ>> \in vote_msg))
Inv680_1_3_def == \A VARI \in Node : \A VALI \in Value : (leader[VARI]) \/ (~(<<VARI,VALI>> \in decided))
Inv7155_2_4_def == \A VARJ \in Node : \A VARK \in Node : (VARJ=VARK) \/ (~(leader[VARJ]) \/ (~(leader[VARK])))
Inv7039_2_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARJ=VARK) \/ (~(<<VARI,VARJ>> \in vote_msg) \/ (~(<<VARI,VARK>> \in vote_msg)))
Inv2245_2_1_def == \A VARI \in Node : \A VARJ \in Node : (<<VARI,VARJ>> \in votes) \/ (~(leader[VARI])) \/ (~(VARJ \in voting_quorum))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv358_1_0_def
  /\ Inv119_1_1_def
  /\ Inv759_1_2_def
  /\ Inv680_1_3_def
  /\ Inv7155_2_4_def
  /\ Inv7039_2_0_def
  /\ Inv2245_2_1_def

  
AXIOM QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
AXIOM EmptyNotInQuorums == {} \notin Quorum \* because quorums are majority sets
AXIOM QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
AXIOM Fin == IsFiniteSet(Node)

LEMMA QuorumsInNode ==
ASSUME IndAuto
PROVE \A k \in voting_quorum : k \in Node
BY QuorumsAreNodePowersets DEF IndAuto, TypeOK


\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF 
    SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
    SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
    TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
  <1>2. Safety'
    BY DEF 
    SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
    SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
    TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
  <1>3. Inv358_1_0_def'
    <2>1. CASE SendRequestVoteAction
      BY <2>1 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>2. CASE SendVoteAction
      BY <2>2 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>3. CASE RecvVoteAction
      BY <2>3 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>4. CASE ChooseVotingQuorumAction
      BY <2>4 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>5. CASE BecomeLeaderAction
      BY <2>5 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>6. CASE DecideAction
      BY <2>6 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    
  <1>4. Inv119_1_1_def'
    <2>1. CASE SendRequestVoteAction
      BY <2>1 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>2. CASE SendVoteAction
      BY <2>2 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>3. CASE RecvVoteAction
      BY <2>3 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>4. CASE ChooseVotingQuorumAction
      BY <2>4 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>5. CASE BecomeLeaderAction
      BY <2>5 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>6. CASE DecideAction
      BY <2>6 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    
  <1>5. Inv759_1_2_def'
    <2>1. CASE SendRequestVoteAction
      BY <2>1 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>2. CASE SendVoteAction
      BY <2>2 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>3. CASE RecvVoteAction
      BY <2>3 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>4. CASE ChooseVotingQuorumAction
      BY <2>4 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>5. CASE BecomeLeaderAction
      BY <2>5 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>6. CASE DecideAction
      BY <2>6 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    
  <1>6. Inv680_1_3_def'
    <2>1. CASE SendRequestVoteAction
      BY <2>1 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>2. CASE SendVoteAction
      BY <2>2 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>3. CASE RecvVoteAction
      BY <2>3 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>4. CASE ChooseVotingQuorumAction
      BY <2>4 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>5. CASE BecomeLeaderAction
      BY <2>5 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>6. CASE DecideAction
      BY <2>6 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    
  <1>7. Inv7155_2_4_def'
    <2>1. CASE SendRequestVoteAction
      BY <2>1 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>2. CASE SendVoteAction
      BY <2>2 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>3. CASE RecvVoteAction
      BY <2>3 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>4. CASE ChooseVotingQuorumAction
      BY <2>4 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>5. CASE BecomeLeaderAction
         <3>1. PICK i \in Node : BecomeLeader(i) BY <2>5 DEF BecomeLeaderAction
         <3>2. leader'[i] = TRUE BY <3>1 DEF BecomeLeader, BecomeLeaderAction,IndAuto, TypeOK
         <3>3. SUFFICES ASSUME NEW j \in Node, leader'[j] = TRUE, j # i
                   PROVE FALSE
                   BY <3>2 DEF Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>4. leader[j] = TRUE BY <3>1, <3>3 DEF BecomeLeader, BecomeLeaderAction, IndAuto, TypeOK
         <3>5. \A k \in Node : (k \in voting_quorum) => <<j,k>> \in votes BY <3>3, <3>4 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>6. \A k \in Node : (k \in voting_quorum) => <<i,k>> \in votes BY <3>1 DEF BecomeLeader, BecomeLeaderAction,IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>7. \A k \in Node : (k \in voting_quorum) => <<k,j>> \in vote_msg BY <3>5 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>8. \A k \in Node : (k \in voting_quorum) => <<k,i>> \in vote_msg BY <3>6 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>9. \A k \in Node : (k \in voting_quorum) => <<k,i>> \notin vote_msg BY <3>3, <3>7 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>10. voting_quorum # {} BY <3>1 DEF BecomeLeader
         <3>11. QED BY <3>8, <3>9, <3>10, QuorumsInNode    
    <2>6. CASE DecideAction
      BY <2>6 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    
  <1>8. Inv7039_2_0_def'
    BY DEF 
    SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
    SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
    TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
  <1>9. Inv2245_2_1_def'
    <2>1. CASE SendRequestVoteAction
      BY <2>1 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>2. CASE SendVoteAction
      BY <2>2 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>3. CASE RecvVoteAction
      BY <2>3 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>4. CASE ChooseVotingQuorumAction
         <3>1. SUFFICES ASSUME NEW i \in Node,
                               NEW j \in Node,
                               leader'[i],
                               j \in voting_quorum'
               PROVE <<i,j>> \in votes' BY DEF Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>2. leader[i] BY <2>4, <3>1 DEF ChooseVotingQuorum,ChooseVotingQuorumAction
         \* this case split actually isn't necessary, only case <3>3 is needed
         <3>3. CASE j \notin voting_quorum
             <4>1. PICK L \in Node : ChooseVotingQuorum(L) BY <2>4 DEF ChooseVotingQuorumAction
             <4>2. PICK Q \in Quorum : (\A v \in Q : <<L,v>> \in votes) /\ voting_quorum' = Q BY <4>1 DEF ChooseVotingQuorum
             <4>3. PICK n \in Node : n \in voting_quorum BY EmptyNotInQuorums, QuorumsInNode DEF IndAuto, TypeOK
             <4>4. <<i,n>> \in votes BY <3>2, <4>3 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
             <4>5. PICK m \in Node : m \in voting_quorum /\ m \in Q BY <4>2, <4>3, QuorumsOverlap, QuorumsInNode DEF IndAuto, TypeOK
             <4>6. <<L,m>> \in votes BY <4>2, <4>5
             <4>7. <<i,m>> \in votes BY <3>2, <4>5 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
             <4>8. i = L
                 <5>1. <<m,L>> \in vote_msg BY <4>6 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
                 <5>. QED BY <5>1, <4>7 DEF IndAuto, Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
             <4>9. <<L,j>> \in votes BY <1>1, <2>4, <3>1, <4>1 DEF ChooseVotingQuorum, IndAuto, TypeOK
             <4>. QED BY <4>1, <4>8, <4>9 DEF ChooseVotingQuorum,TypeOK,IndAuto,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>4. CASE j \in voting_quorum
             BY <2>4, <3>1, <3>2, <3>4 DEF ChooseVotingQuorum,ChooseVotingQuorumAction,TypeOK,IndAuto,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
         <3>. QED BY <3>3, <3>4
 
    <2>5. CASE BecomeLeaderAction
      BY <2>5 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>6. CASE DecideAction
      BY <2>6 DEF 
      SendRequestVote,SendVote,RecvVote,ChooseVotingQuorum,BecomeLeader,Decide,
      SendRequestVoteAction,SendVoteAction,RecvVoteAction,ChooseVotingQuorumAction,BecomeLeaderAction,DecideAction,
      TypeOK,Init,Next,IndAuto,Safety,Inv358_1_0_def,Inv119_1_1_def,Inv759_1_2_def,Inv680_1_3_def,Inv7155_2_4_def,Inv7039_2_0_def,Inv2245_2_1_def
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    
  <1>10. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
    
====
