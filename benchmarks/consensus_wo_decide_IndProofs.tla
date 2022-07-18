---- MODULE consensus_wo_decide_IndProofs ----
EXTENDS consensus_wo_decide, TLAPS

\* endive.py stats
\* -----------------
\* date: 2022-08-03T22:39:17.807250
\* is_inductive: True
\* inv_size: 8
\* invcheck_duration_secs: 44.933435678482056
\* ctielimcheck_duration_secs: 39.60547208786011
\* ctigen_duration_secs: 21.769129991531372
\* total_duration_secs: 106.41932106018066
\* total_num_ctis_eliminated: 12995
\* total_num_cti_elimination_rounds: 2
\* total_num_invs_generated: 857
\* total_num_invs_checked: 16184
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 10
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv434_1_0_def == \A VARI \in Node : \A VARJ \in Node : (vote_request_msg[<<VARI,VARJ>>]) \/ (~(votes[<<VARI,VARJ>>]))
Inv306_1_1_def == \A VARI \in Node : \A VARJ \in Node : (vote_msg[<<VARI,VARJ>>]) \/ (~(votes[<<VARJ,VARI>>]))
Inv426_1_2_def == \A VARI \in Node : \A VARJ \in Node : (vote_request_msg[<<VARI,VARJ>>]) \/ (~(vote_msg[<<VARJ,VARI>>]))
Inv550_1_3_def == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(votes[<<VARJ,VARI>>]))
Inv6986_2_4_def == \A VARI \in Node : \A VARJ \in Node : (votes[<<VARI,VARJ>>]) \/ (~(VARJ \in voting_quorum) \/ (~(leader[VARI])))
Inv538_1_0_def == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(vote_msg[<<VARI,VARJ>>]))
Inv1559_2_1_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARJ=VARK) \/ (~(vote_msg[<<VARI,VARK>>])) \/ (~(vote_msg[<<VARI,VARJ>>]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv434_1_0_def
  /\ Inv306_1_1_def
  /\ Inv426_1_2_def
  /\ Inv550_1_3_def
  /\ Inv6986_2_4_def
  /\ Inv538_1_0_def
  /\ Inv1559_2_1_def

AXIOM QuorumsAreNodePowersets == Quorums \subseteq SUBSET Node
AXIOM EmptyNotInQuorums == {} \notin Quorums \* because quorums are majority sets
AXIOM QuorumsOverlap == \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}

LEMMA QuorumsInNode ==
ASSUME IndAuto
PROVE \A k \in voting_quorum : k \in Node
BY QuorumsAreNodePowersets DEF IndAuto, TypeOK

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto
BY DEF TypeOK,Init,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def

THEOREM IndAuto /\ Next => IndAuto'
    <1>. SUFFICES ASSUME IndAuto, Next
         PROVE IndAuto'
         OBVIOUS
    <1>1. TypeOK'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>5. CASE \E i \in Node : BecomeLeader(i)
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>2. Safety'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>5. CASE \E i \in Node : BecomeLeader(i)
            <3>1. PICK i \in Node : BecomeLeader(i) BY <2>5
            <3>2. leader'[i] = TRUE BY <3>1 DEF BecomeLeader, IndAuto, TypeOK
            <3>3. SUFFICES ASSUME NEW j \in Node, leader'[j] = TRUE, j # i
                  PROVE FALSE
                  BY <3>2 DEF Safety
            <3>4. leader[j] = TRUE BY <3>1, <3>3 DEF BecomeLeader, IndAuto, TypeOK
            <3>5. \A k \in Node : (k \in voting_quorum) => votes[<<j,k>>] BY <3>3, <3>4 DEF IndAuto, Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            <3>6. \A k \in Node : (k \in voting_quorum) => votes[<<i,k>>] BY <3>1 DEF BecomeLeader
            <3>7. \A k \in Node : (k \in voting_quorum) => vote_msg[<<k,j>>] BY <3>5 DEF IndAuto, Inv306_1_1_def
            <3>8. \A k \in Node : (k \in voting_quorum) => vote_msg[<<k,i>>] BY <3>6 DEF IndAuto, Inv306_1_1_def
            <3>9. \A k \in Node : (k \in voting_quorum) => ~vote_msg[<<k,i>>] BY <3>3, <3>7 DEF IndAuto, Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            <3>10. voting_quorum # {} BY <3>1 DEF BecomeLeader
            <3>. QED BY <3>8, <3>9, <3>10, QuorumsInNode
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next

    <1>3. Inv434_1_0_def'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            <3>1. PICK i,j \in Node : RecvVote(i,j) BY <2>3
            <3>2. vote_msg[<<j,i>>] BY <3>1 DEF RecvVote
            <3>. QED BY <3>1, <3>2 DEF RecvVote, IndAuto, Inv426_1_2_def, Inv434_1_0_def, TypeOK
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((vote_request_msg[<<VARI,VARJ>>]) \/ (~(votes[<<VARI,VARJ>>])))'
            BY DEF Inv434_1_0_def
          <3> QED
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>5. CASE \E i \in Node : BecomeLeader(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((vote_request_msg[<<VARI,VARJ>>]) \/ (~(votes[<<VARI,VARJ>>])))'
            BY DEF Inv434_1_0_def
          <3> QED
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>4. Inv306_1_1_def'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((vote_msg[<<VARI,VARJ>>]) \/ (~(votes[<<VARJ,VARI>>])))'
            BY DEF Inv306_1_1_def
          <3> QED
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>5. CASE \E i \in Node : BecomeLeader(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((vote_msg[<<VARI,VARJ>>]) \/ (~(votes[<<VARJ,VARI>>])))'
            BY DEF Inv306_1_1_def
          <3> QED
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>5. Inv426_1_2_def'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <1>1, <2>1 DEF SendRequestVote,TypeOK,IndAuto,Inv426_1_2_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            <3>1. PICK p,q \in Node : SendVote(p,q) BY <2>2
            <3>2. SUFFICES \A i,j,k \in Node : ~(vote_msg'[<<i,j>>]) \/ ((vote_request_msg'[<<j,i>>]) /\ (TRUE))
                BY DEF Inv426_1_2_def
            <3>.  TAKE i,j,k \in Node
            <3>3. CASE p = i /\ q = j BY <3>1, <3>3 DEF SendVote
            <3>4. CASE p # i \/ q # j BY <3>1, <3>4 DEF SendVote, IndAuto, Inv426_1_2_def, TypeOK
            <3>. QED BY <3>3, <3>4
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((vote_request_msg[<<VARI,VARJ>>]) \/ (~(vote_msg[<<VARJ,VARI>>])))'
            BY DEF Inv426_1_2_def
          <3> QED
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>5. CASE \E i \in Node : BecomeLeader(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((vote_request_msg[<<VARI,VARJ>>]) \/ (~(vote_msg[<<VARJ,VARI>>])))'
            BY DEF Inv426_1_2_def
          <3> QED
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>6. Inv550_1_3_def'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((voted[VARI]) \/ (~(votes[<<VARJ,VARI>>])))'
            BY DEF Inv550_1_3_def
          <3> QED
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>5. CASE \E i \in Node : BecomeLeader(i)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((voted[VARI]) \/ (~(votes[<<VARJ,VARI>>])))'
            BY DEF Inv550_1_3_def
          <3> QED
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>7. Inv538_1_0_def'
      <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
        BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
      <2>2. CASE \E i,j \in Node : SendVote(i,j)
        <3> SUFFICES ASSUME NEW VARI \in Node',
                            NEW VARJ \in Node'
                     PROVE  ((voted[VARI]) \/ (~(vote_msg[<<VARI,VARJ>>])))'
          BY DEF Inv538_1_0_def
        <3> QED
          BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        
      <2>3. CASE \E i,j \in Node : RecvVote(i,j)
        BY <2>3 DEF RecvVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
      <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
        <3> SUFFICES ASSUME NEW VARI \in Node',
                            NEW VARJ \in Node'
                     PROVE  ((voted[VARI]) \/ (~(vote_msg[<<VARI,VARJ>>])))'
          BY DEF Inv538_1_0_def
        <3> QED
          BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        
      <2>5. CASE \E i \in Node : BecomeLeader(i)
        <3> SUFFICES ASSUME NEW VARI \in Node',
                            NEW VARJ \in Node'
                     PROVE  ((voted[VARI]) \/ (~(vote_msg[<<VARI,VARJ>>])))'
          BY DEF Inv538_1_0_def
        <3> QED
          BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def       
      <2>6. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>8. Inv1559_2_1_def'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
            <3>1. SUFFICES ASSUME NEW i \in Node,
                                  NEW j \in Node,
                                  NEW k \in Node,
                                  vote_msg'[<<i,j>>],
                                  vote_msg'[<<i,k>>],
                                  j#k
                  PROVE FALSE BY DEF Inv1559_2_1_def
            <3>2. PICK p,q \in Node : SendVote(p,q) BY <2>2
            <3>3. p = i BY <3>1, <3>2 DEF SendVote, IndAuto, TypeOK, Inv1559_2_1_def
            <3>4. q = j \/ q = k BY <3>1, <3>2, <3>3 DEF SendVote, IndAuto, TypeOK, Inv1559_2_1_def
            <3>5. CASE q = j
                <4>1. vote_request_msg[<<j,i>>] BY <3>2, <3>3, <3>5 DEF SendVote
                <4>2. vote_msg[<<i,k>>] BY <3>1, <3>2, <3>3, <3>5 DEF SendVote, IndAuto, TypeOK
                <4>3. voted[i] BY <4>2 DEF IndAuto,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
                <4>. QED BY <3>2, <3>3, <4>3 DEF SendVote
            <3>6. CASE q = k
                <4>1. vote_request_msg[<<k,i>>] BY <3>2, <3>3, <3>6 DEF SendVote
                <4>2. vote_msg[<<i,j>>] BY <3>1, <3>2, <3>3, <3>5 DEF SendVote, IndAuto, TypeOK
                <4>3. voted[i] BY <4>2 DEF IndAuto,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
                <4>. QED BY <3>2, <3>3, <4>3 DEF SendVote
            <3>. QED BY <3>4, <3>5, <3>6
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Inv1559_2_1_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
            BY <2>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Inv1559_2_1_def
        <2>5. CASE \E i \in Node : BecomeLeader(i)
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Inv1559_2_1_def
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    <1>9. Inv6986_2_4_def'
        <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
            BY <2>1 DEF SendRequestVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
        <2>2. CASE \E i,j \in Node : SendVote(i,j)
          <3> SUFFICES ASSUME NEW VARI \in Node',
                              NEW VARJ \in Node'
                       PROVE  ((votes[<<VARI,VARJ>>]) \/ (~(VARJ \in voting_quorum) \/ (~(leader[VARI]))))'
            BY DEF Inv6986_2_4_def
          <3> QED
            BY <2>2 DEF SendVote,TypeOK,IndAuto,Safety,Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
            
        <2>3. CASE \E i,j \in Node : RecvVote(i,j)
            BY <2>3 DEF RecvVote,TypeOK,IndAuto,Inv6986_2_4_def
        <2>4. CASE \E i \in Node : ChooseVotingQuorum(i)
            <3>1. SUFFICES ASSUME NEW i \in Node,
                                  NEW j \in Node,
                                  leader'[i],
                                  j \in voting_quorum'
                  PROVE votes'[<<i,j>>] BY DEF Inv6986_2_4_def
            <3>2. leader[i] BY <2>4, <3>1 DEF ChooseVotingQuorum
            \* this case split actually isn't necessary, only case <3>3 is needed
            <3>3. CASE j \notin voting_quorum
                <4>1. PICK L \in Node : ChooseVotingQuorum(L) BY <2>4
                <4>2. PICK Q \in Quorums : (\A v \in Q : votes[<<L,v>>]) /\ voting_quorum' = Q BY <4>1 DEF ChooseVotingQuorum
                <4>3. PICK n \in Node : n \in voting_quorum BY EmptyNotInQuorums, QuorumsInNode DEF IndAuto, TypeOK
                <4>4. votes[<<i,n>>] BY <3>2, <4>3 DEF IndAuto, Inv6986_2_4_def
                <4>5. PICK m \in Node : m \in voting_quorum /\ m \in Q BY <4>2, <4>3, QuorumsOverlap, QuorumsInNode DEF IndAuto, TypeOK
                <4>6. votes[<<L,m>>] BY <4>2, <4>5
                <4>7. votes[<<i,m>>] BY <3>2, <4>5 DEF IndAuto, Inv6986_2_4_def
                <4>8. i = L
                    <5>1. vote_msg[<<m,L>>] BY <4>6 DEF IndAuto, Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
                    <5>. QED BY <5>1, <4>7 DEF IndAuto, Inv6986_2_4_def, Inv434_1_0_def,Inv306_1_1_def,Inv426_1_2_def,Inv550_1_3_def,Inv6986_2_4_def,Inv538_1_0_def,Inv1559_2_1_def
                <4>9. votes[<<L,j>>] BY <1>1, <2>4, <3>1, <4>1 DEF ChooseVotingQuorum, IndAuto, TypeOK
                <4>. QED BY <4>1, <4>8, <4>9 DEF ChooseVotingQuorum,TypeOK,IndAuto,Inv1559_2_1_def
            <3>4. CASE j \in voting_quorum
                BY <2>4, <3>1, <3>2, <3>4 DEF ChooseVotingQuorum,TypeOK,IndAuto,Inv1559_2_1_def,Inv6986_2_4_def
            <3>. QED BY <3>3, <3>4
        <2>5. CASE \E i \in Node : BecomeLeader(i)
            BY <2>5 DEF BecomeLeader,TypeOK,IndAuto,Inv1559_2_1_def,Inv6986_2_4_def
        <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next

    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto

====

