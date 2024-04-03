---- MODULE consensus_epr_IndProofs ----
EXTENDS consensus_epr, FiniteSetTheorems,TLAPS

\* endive.py stats
\* -----------------
\* date: 2022-08-05T22:43:54.943748
\* is_inductive: True
\* inv_size: 8
\* invcheck_duration_secs: 121.35228300094604
\* ctielimcheck_duration_secs: 45.64810538291931
\* ctigen_duration_secs: 110.43368673324585
\* total_duration_secs: 277.5921528339386
\* total_num_ctis_eliminated: 16269
\* total_num_cti_elimination_rounds: 3
\* total_num_invs_generated: 1705
\* total_num_invs_checked: 16743
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

\* \* Inductive strengthening conjuncts
\* Inv119_1_0_def == \A VARI \in Node : \A VARJ \in Node : (<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARI]))
\* Inv152_1_1_def == \A VARI \in Node : \E QJ \in Quorum : \A VALI \in Value : (QJ \subseteq votes[VARI]) \/ (~(VALI \in decided[VARI]))
\* Inv693_1_2_def == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(<<VARI,VARJ>> \in vote_msg))
\* Inv164_1_3_def == \A VARI \in Node : \E QJ \in Quorum : (QJ \subseteq votes[VARI]) \/ (~(leader[VARI]))
\* Inv622_1_4_def == \A VARI \in Node : \A VALI \in Value : (leader[VARI]) \/ (~(VALI \in decided[VARI]))
\* Inv4302_2_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARI = VARK /\ votes = votes) \/ (~(<<VARJ,VARI>> \in vote_msg)) \/ (~(VARJ \in votes[VARK]))
\* Inv5288_2_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARJ = VARK /\ votes = votes) \/ (~(<<VARI,VARK>> \in vote_msg)) \/ (~(<<VARI,VARJ>> \in vote_msg))

\* \* The inductive invariant candidate.
\* IndAuto ==
\*   /\ TypeOK
\*   /\ Safety
\*   /\ Inv119_1_0_def
\*   /\ Inv152_1_1_def
\*   /\ Inv693_1_2_def
\*   /\ Inv164_1_3_def
\*   /\ Inv622_1_4_def
\*   /\ Inv4302_2_0_def
\*   /\ Inv5288_2_0_def
  

\* ASSUME QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
\* ASSUME EmptyNotInQuorums == {} \notin Quorum \* because quorums are majority sets
\* ASSUME QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
\* ASSUME Fin == IsFiniteSet(Node)
\* ASSUME NodeNonEmpty == Node # {}
\* ASSUME QuorumsNonEmpty == Quorum # {}
\* ASSUME NodeQuorumType == Fin /\ NodeNonEmpty /\ QuorumsAreNodePowersets /\ EmptyNotInQuorums /\ QuorumsNonEmpty

  
  
\* \* TLAPS Proof skeleton.
\* THEOREM Init => IndAuto 
\*   <1> SUFFICES ASSUME Init
\*                PROVE  IndAuto
\*     OBVIOUS
\*   <1>1. TypeOK
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>2. Safety
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>3. Inv119_1_0_def
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>4. Inv152_1_1_def
\*     BY Fin, NodeNonEmpty,QuorumsAreNodePowersets,NodeQuorumType DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*   <1>5. Inv693_1_2_def
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*   <1>6. Inv164_1_3_def
\*     BY Fin, NodeNonEmpty, QuorumsNonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*   <1>7. Inv622_1_4_def
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>8. Inv4302_2_0_def
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>9. Inv5288_2_0_def
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>10. QED
\*     BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
  

\* THEOREM IndAuto /\ Next => IndAuto'
\*   <1> SUFFICES ASSUME IndAuto /\ Next
\*                PROVE  IndAuto'
\*     OBVIOUS
\*   <1>1. TypeOK'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
\*   <1>2. Safety'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*         <3>. PICK i \in Node, v \in Value : Decide(i,v) BY <2>5 DEF IndAuto,Next
\*         <3>. SUFFICES ASSUME NEW i2 \in Node,
\*                               NEW v2 \in Value,
\*                               v2 \in decided[i2]',
\*                               v2 # v 
\*                               PROVE FALSE
\*                               BY DEF IndAuto,Next,Safety
\*         <3>3. leader[i] BY DEF IndAuto,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,Decide
\*         <3>4. leader'[i] BY DEF IndAuto,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,Decide
\*         <3>5. CASE i2 = i
\*             <4>1. v2 \in decided[i2] BY <3>5 DEF IndAuto,Next,Decide
\*             <4>2. decided[i2] = {} BY <3>5 DEF IndAuto,Next,Decide
\*             <4>3. QED BY <3>5,<4>2, <4>1
\*         <3>6. CASE i2 # i
\*             <4>. v2 \in decided[i2] BY DEF IndAuto,Next,Decide
\*             <4>. PICK Q2 \in Quorum : (Q2 \subseteq votes[i2]) BY DEF 
\*                 IndAuto,TypeOK,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*             <4>. v \in decided'[i] BY DEF IndAuto, TypeOK,Decide, Next
\*             <4>. leader[i] BY DEF IndAuto, TypeOK,Decide, Next
\*             <4>. PICK Q \in Quorum : (Q \subseteq votes[i]) BY DEF 
\*              IndAuto,TypeOK,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*             <4>. PICK ix \in Node : ix \in (Q2 \cap Q) BY QuorumsOverlap DEF IndAuto, TypeOK, NodeQuorumType
\*             <4>. ix \in votes[i] OBVIOUS
\*             <4>. ix \in votes[i2] OBVIOUS
\*             <4>. <<ix,i>> \in vote_msg BY DEF IndAuto, Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*             <4>. <<ix,i2>> \in vote_msg BY DEF IndAuto,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*             <4>. <<ix,i>> \in vote_msg /\ <<ix,i2>> \in vote_msg /\ i # i2 BY <3>6
\*             <4>. voted[ix] BY DEF IndAuto,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*             <4>. QED BY DEF IndAuto,TypeOK,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
\*         <3>9. QED BY <3>5,<3>6

\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
      
\*   <1>3. Inv119_1_0_def'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       <3> SUFFICES ASSUME NEW VARI \in Node',
\*                           NEW VARJ \in Node'
\*                    PROVE  ((<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARI])))'
\*         BY DEF Inv119_1_0_def
\*       <3> QED
\*         BY <2>3,NodeQuorumType DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*         SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
      
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
\*   <1>4. Inv152_1_1_def'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
\*   <1>5. Inv693_1_2_def'
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>6. Inv164_1_3_def'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
\*   <1>7. Inv622_1_4_def'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
\*   <1>8. Inv4302_2_0_def'
\*     <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>2. CASE \E i,j \in Node : SendVote(i,j)
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>3. CASE \E i,j \in Node : RecvVote(i,j)
\*       <3> SUFFICES ASSUME NEW VARI \in Node',
\*                           NEW VARJ \in Node'
\*                    PROVE  (\A VARK \in Node : (VARI = VARK /\ votes = votes) \/ (~(<<VARJ,VARI>> \in vote_msg)) \/ (~(VARJ \in votes[VARK])))'
\*         BY DEF Inv4302_2_0_def
\*       <3> QED
\*         BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*   SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
      
\*     <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*       SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*     <2>6. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
    
\*   <1>9. Inv5288_2_0_def'
\*     BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
\*     SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
\*   <1>10. QED
\*     BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto


---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

\* DISCOVERY 2024

ASSUME QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
ASSUME EmptyNotInQuorums == {} \notin Quorum \* because quorums are majority sets
ASSUME QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME Fin == IsFiniteSet(Node)
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsNonEmpty == Quorum # {}
ASSUME NodeQuorumType == Fin /\ NodeNonEmpty /\ QuorumsAreNodePowersets /\ EmptyNotInQuorums /\ QuorumsNonEmpty

USE Fin, QuorumsAreNodePowersets, EmptyNotInQuorums, QuorumsOverlap, NodeNonEmpty, QuorumsNonEmpty, NodeQuorumType

\* Proof Graph Stats
\* ==================
\* num proof graph nodes: 10
\* num proof obligations: 50
Safety == H_NoConflictingValues
Inv254_R0_0_I2 == \A VARI \in Node : \A VARJ \in Node : (decided[VARI] = {}) \/ (~(decided[VARJ] = {}) \/ (~(leader[VARJ])))
Inv1054_R1_0_I2 == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (NodesEq(VARI, VARK)) \/ (~(VARJ \in votes[VARI])) \/ (~(VARJ \in votes[VARK]))
Inv367_R1_0_I2 == \A VARI \in Node : \E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ ((decided[VARI] = {}))
Inv210_R1_1_I2 == \A VARI \in Node : \A VARJ \in Node : (VARI = VARJ /\ leader = leader) \/ (~(leader[VARJ])) \/ (~(leader[VARI]))
Inv1248_R2_0_I2 == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (NodesEq(VARI, VARK)) \/ (~(<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARK])))
Inv389_R3_0_I1 == \A VARI \in Node : \E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ (~(leader[VARI]))
Inv1435_R5_0_I2 == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (NodesEq(VARJ, VARK)) \/ (~(<<VARI,VARJ>> \in vote_msg)) \/ (~(<<VARI,VARK>> \in vote_msg))
Inv368_R5_1_I1 == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(VARI \in votes[VARJ]))
Inv362_R7_0_I1 == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(<<VARI,VARJ>> \in vote_msg))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv254_R0_0_I2
  /\ Inv1054_R1_0_I2
  /\ Inv1248_R2_0_I2
  /\ Inv1435_R5_0_I2
  /\ Inv362_R7_0_I1
  /\ Inv368_R5_1_I1
  /\ Inv367_R1_0_I2
  /\ Inv389_R3_0_I1
  /\ Inv210_R1_1_I2


\* mean in-degree: 0.9
\* median in-degree: 1
\* max in-degree: 3
\* min in-degree: 0
\* mean variable slice size: 0

USE DEF NodesEq

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,SendRequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ SendRequestVoteAction => TypeOK'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,TypeOK
  \* (TypeOK,SendVoteAction)
  <1>2. TypeOK /\ TypeOK /\ SendVoteAction => TypeOK'
       BY DEF TypeOK,SendVoteAction,SendVote,TypeOK
  \* (TypeOK,RecvVoteAction)
  <1>3. TypeOK /\ TypeOK /\ RecvVoteAction => TypeOK'
       BY DEF TypeOK,RecvVoteAction,RecvVote,TypeOK
  \* (TypeOK,BecomeLeaderAction)
  <1>4. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,DecideAction)
  <1>5. TypeOK /\ TypeOK /\ DecideAction => TypeOK'
       BY DEF TypeOK,DecideAction,Decide,TypeOK
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv254_R0_0_I2 /\ Safety /\ Next => Safety'
  \* (Safety,SendRequestVoteAction)
  <1>1. TypeOK /\ Safety /\ SendRequestVoteAction => Safety'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Safety,H_NoConflictingValues
  \* (Safety,SendVoteAction)
  <1>2. TypeOK /\ Safety /\ SendVoteAction => Safety'
       BY DEF TypeOK,SendVoteAction,SendVote,Safety,H_NoConflictingValues
  \* (Safety,RecvVoteAction)
  <1>3. TypeOK /\ Safety /\ RecvVoteAction => Safety'
       BY DEF TypeOK,RecvVoteAction,RecvVote,Safety,H_NoConflictingValues
  \* (Safety,BecomeLeaderAction)
  <1>4. TypeOK /\ Safety /\ BecomeLeaderAction => Safety'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Safety,H_NoConflictingValues
  \* (Safety,DecideAction)
  <1>5. TypeOK /\ Inv254_R0_0_I2 /\ Safety /\ DecideAction => Safety'
       BY DEF TypeOK,Inv254_R0_0_I2,DecideAction,Decide,Safety,H_NoConflictingValues
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv254_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv1054_R1_0_I2 /\ Inv367_R1_0_I2 /\ Inv210_R1_1_I2 /\ Inv254_R0_0_I2 /\ Next => Inv254_R0_0_I2'
  \* (Inv254_R0_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv254_R0_0_I2 /\ SendRequestVoteAction => Inv254_R0_0_I2'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv254_R0_0_I2
  \* (Inv254_R0_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv254_R0_0_I2 /\ SendVoteAction => Inv254_R0_0_I2'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv254_R0_0_I2
  \* (Inv254_R0_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv254_R0_0_I2 /\ RecvVoteAction => Inv254_R0_0_I2'
       BY DEF TypeOK,RecvVoteAction,RecvVote,Inv254_R0_0_I2
  \* (Inv254_R0_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1054_R1_0_I2 /\ Inv367_R1_0_I2 /\ Inv254_R0_0_I2 /\ BecomeLeaderAction => Inv254_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK /\ Inv1054_R1_0_I2 /\ Inv367_R1_0_I2 /\ Inv254_R0_0_I2 /\ BecomeLeaderAction,
                        NEW VARI \in Node',
                        NEW VARJ \in Node'
                 PROVE  ((decided[VARI] = {}) \/ (~(decided[VARJ] = {}) \/ (~(leader[VARJ]))))'
      BY DEF Inv254_R0_0_I2
    <2> QED
      BY DEF TypeOK,Inv1054_R1_0_I2,Inv367_R1_0_I2,BecomeLeaderAction,BecomeLeader,Inv254_R0_0_I2
       
  \* (Inv254_R0_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv210_R1_1_I2 /\ Inv254_R0_0_I2 /\ DecideAction => Inv254_R0_0_I2'
       BY DEF TypeOK,Inv210_R1_1_I2,DecideAction,Decide,Inv254_R0_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv1054_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv1248_R2_0_I2 /\ Inv1054_R1_0_I2 /\ Next => Inv1054_R1_0_I2'
  \* (Inv1054_R1_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv1054_R1_0_I2 /\ SendRequestVoteAction => Inv1054_R1_0_I2'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv1054_R1_0_I2
  \* (Inv1054_R1_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv1054_R1_0_I2 /\ SendVoteAction => Inv1054_R1_0_I2'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv1054_R1_0_I2
  \* (Inv1054_R1_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv1248_R2_0_I2 /\ Inv1054_R1_0_I2 /\ RecvVoteAction => Inv1054_R1_0_I2'
       BY DEF TypeOK,Inv1248_R2_0_I2,RecvVoteAction,RecvVote,Inv1054_R1_0_I2
  \* (Inv1054_R1_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1054_R1_0_I2 /\ BecomeLeaderAction => Inv1054_R1_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1054_R1_0_I2
  \* (Inv1054_R1_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv1054_R1_0_I2 /\ DecideAction => Inv1054_R1_0_I2'
       BY DEF TypeOK,DecideAction,Decide,Inv1054_R1_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv1248_R2_0_I2
THEOREM L_4 == TypeOK /\ Inv368_R5_1_I1 /\ Inv1435_R5_0_I2 /\ Inv1248_R2_0_I2 /\ Next => Inv1248_R2_0_I2'
  \* (Inv1248_R2_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv1248_R2_0_I2 /\ SendRequestVoteAction => Inv1248_R2_0_I2'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv1248_R2_0_I2
  \* (Inv1248_R2_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv368_R5_1_I1 /\ Inv1248_R2_0_I2 /\ SendVoteAction => Inv1248_R2_0_I2'
       BY DEF TypeOK,Inv368_R5_1_I1,SendVoteAction,SendVote,Inv1248_R2_0_I2
  \* (Inv1248_R2_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv1435_R5_0_I2 /\ Inv1248_R2_0_I2 /\ RecvVoteAction => Inv1248_R2_0_I2'
    <2> SUFFICES ASSUME TypeOK /\ Inv1435_R5_0_I2 /\ Inv1248_R2_0_I2 /\ RecvVoteAction,
                        NEW VARI \in Node',
                        NEW VARJ \in Node',
                        NEW VARK \in Node'
                 PROVE  ((NodesEq(VARI, VARK)) \/ (~(<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARK]))))'
      BY DEF Inv1248_R2_0_I2
    <2> QED
      BY DEF TypeOK,Inv1435_R5_0_I2,RecvVoteAction,RecvVote,Inv1248_R2_0_I2
       
  \* (Inv1248_R2_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1248_R2_0_I2 /\ BecomeLeaderAction => Inv1248_R2_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1248_R2_0_I2
  \* (Inv1248_R2_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv1248_R2_0_I2 /\ DecideAction => Inv1248_R2_0_I2'
       BY DEF TypeOK,DecideAction,Decide,Inv1248_R2_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv1435_R5_0_I2
THEOREM L_5 == TypeOK /\ Inv362_R7_0_I1 /\ Inv1435_R5_0_I2 /\ Next => Inv1435_R5_0_I2'
  \* (Inv1435_R5_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv1435_R5_0_I2 /\ SendRequestVoteAction => Inv1435_R5_0_I2'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv1435_R5_0_I2
  \* (Inv1435_R5_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv362_R7_0_I1 /\ Inv1435_R5_0_I2 /\ SendVoteAction => Inv1435_R5_0_I2'
       BY DEF TypeOK,Inv362_R7_0_I1,SendVoteAction,SendVote,Inv1435_R5_0_I2
  \* (Inv1435_R5_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv1435_R5_0_I2 /\ RecvVoteAction => Inv1435_R5_0_I2'
       BY DEF TypeOK,RecvVoteAction,RecvVote,Inv1435_R5_0_I2
  \* (Inv1435_R5_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv1435_R5_0_I2 /\ BecomeLeaderAction => Inv1435_R5_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1435_R5_0_I2
  \* (Inv1435_R5_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv1435_R5_0_I2 /\ DecideAction => Inv1435_R5_0_I2'
       BY DEF TypeOK,DecideAction,Decide,Inv1435_R5_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv362_R7_0_I1
THEOREM L_6 == TypeOK /\ Inv362_R7_0_I1 /\ Next => Inv362_R7_0_I1'
  \* (Inv362_R7_0_I1,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv362_R7_0_I1 /\ SendRequestVoteAction => Inv362_R7_0_I1'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv362_R7_0_I1
  \* (Inv362_R7_0_I1,SendVoteAction)
  <1>2. TypeOK /\ Inv362_R7_0_I1 /\ SendVoteAction => Inv362_R7_0_I1'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv362_R7_0_I1
  \* (Inv362_R7_0_I1,RecvVoteAction)
  <1>3. TypeOK /\ Inv362_R7_0_I1 /\ RecvVoteAction => Inv362_R7_0_I1'
       BY DEF TypeOK,RecvVoteAction,RecvVote,Inv362_R7_0_I1
  \* (Inv362_R7_0_I1,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv362_R7_0_I1 /\ BecomeLeaderAction => Inv362_R7_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv362_R7_0_I1
  \* (Inv362_R7_0_I1,DecideAction)
  <1>5. TypeOK /\ Inv362_R7_0_I1 /\ DecideAction => Inv362_R7_0_I1'
       BY DEF TypeOK,DecideAction,Decide,Inv362_R7_0_I1
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv368_R5_1_I1
THEOREM L_7 == TypeOK /\ Inv368_R5_1_I1 /\ Next => Inv368_R5_1_I1'
  \* (Inv368_R5_1_I1,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv368_R5_1_I1 /\ SendRequestVoteAction => Inv368_R5_1_I1'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv368_R5_1_I1
  \* (Inv368_R5_1_I1,SendVoteAction)
  <1>2. TypeOK /\ Inv368_R5_1_I1 /\ SendVoteAction => Inv368_R5_1_I1'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv368_R5_1_I1
  \* (Inv368_R5_1_I1,RecvVoteAction)
  <1>3. TypeOK /\ Inv368_R5_1_I1 /\ RecvVoteAction => Inv368_R5_1_I1'
    <2> SUFFICES ASSUME TypeOK /\ Inv368_R5_1_I1 /\ RecvVoteAction,
                        NEW VARI \in Node',
                        NEW VARJ \in Node'
                 PROVE  ((voted[VARI]) \/ (~(VARI \in votes[VARJ])))'
      BY DEF Inv368_R5_1_I1
    <2> QED
      <3> SUFFICES ASSUME NEW i \in Node, NEW j \in Node,
                          RecvVote(i,j)
                   PROVE  ((voted[VARI]) \/ (~(VARI \in votes[VARJ])))'
        BY DEF RecvVoteAction
      <3> QED
        BY DEF TypeOK,RecvVoteAction,RecvVote,Inv368_R5_1_I1
      
       
  \* (Inv368_R5_1_I1,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv368_R5_1_I1 /\ BecomeLeaderAction => Inv368_R5_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv368_R5_1_I1
  \* (Inv368_R5_1_I1,DecideAction)
  <1>5. TypeOK /\ Inv368_R5_1_I1 /\ DecideAction => Inv368_R5_1_I1'
       BY DEF TypeOK,DecideAction,Decide,Inv368_R5_1_I1
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv367_R1_0_I2
THEOREM L_8 == TypeOK /\ Inv389_R3_0_I1 /\ Inv367_R1_0_I2 /\ Next => Inv367_R1_0_I2'
  \* (Inv367_R1_0_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv367_R1_0_I2 /\ SendRequestVoteAction => Inv367_R1_0_I2'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv367_R1_0_I2
  \* (Inv367_R1_0_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv367_R1_0_I2 /\ SendVoteAction => Inv367_R1_0_I2'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv367_R1_0_I2
  \* (Inv367_R1_0_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv367_R1_0_I2 /\ RecvVoteAction => Inv367_R1_0_I2'
    <2> SUFFICES ASSUME TypeOK /\ Inv367_R1_0_I2 /\ RecvVoteAction,
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ ((decided[VARI] = {})))'
      BY DEF Inv367_R1_0_I2
    <2> QED
      BY DEF TypeOK,RecvVoteAction,RecvVote,Inv367_R1_0_I2
       
  \* (Inv367_R1_0_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv367_R1_0_I2 /\ BecomeLeaderAction => Inv367_R1_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv367_R1_0_I2
  \* (Inv367_R1_0_I2,DecideAction)
  <1>5. TypeOK /\ Inv389_R3_0_I1 /\ Inv367_R1_0_I2 /\ DecideAction => Inv367_R1_0_I2'
       BY DEF TypeOK,Inv389_R3_0_I1,DecideAction,Decide,Inv367_R1_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv389_R3_0_I1
THEOREM L_9 == TypeOK /\ Inv389_R3_0_I1 /\ Next => Inv389_R3_0_I1'
  \* (Inv389_R3_0_I1,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv389_R3_0_I1 /\ SendRequestVoteAction => Inv389_R3_0_I1'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv389_R3_0_I1
  \* (Inv389_R3_0_I1,SendVoteAction)
  <1>2. TypeOK /\ Inv389_R3_0_I1 /\ SendVoteAction => Inv389_R3_0_I1'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv389_R3_0_I1
  \* (Inv389_R3_0_I1,RecvVoteAction)
  <1>3. TypeOK /\ Inv389_R3_0_I1 /\ RecvVoteAction => Inv389_R3_0_I1'
    <2> SUFFICES ASSUME TypeOK /\ Inv389_R3_0_I1 /\ RecvVoteAction,
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ (~(leader[VARI])))'
      BY DEF Inv389_R3_0_I1
    <2> QED
      BY DEF TypeOK,RecvVoteAction,RecvVote,Inv389_R3_0_I1
       
  \* (Inv389_R3_0_I1,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv389_R3_0_I1 /\ BecomeLeaderAction => Inv389_R3_0_I1'
    <2> SUFFICES ASSUME TypeOK /\ Inv389_R3_0_I1 /\ BecomeLeaderAction,
                        NEW VARI \in Node'
                 PROVE  (\E VARQJ \in Quorum : (VARQJ = votes[VARI]) \/ (~(leader[VARI])))'
      BY DEF Inv389_R3_0_I1
    <2> QED
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv389_R3_0_I1
       
  \* (Inv389_R3_0_I1,DecideAction)
  <1>5. TypeOK /\ Inv389_R3_0_I1 /\ DecideAction => Inv389_R3_0_I1'
       BY DEF TypeOK,DecideAction,Decide,Inv389_R3_0_I1
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


\*** Inv210_R1_1_I2
THEOREM L_10 == TypeOK /\ Inv210_R1_1_I2 /\ Next => Inv210_R1_1_I2'
  \* (Inv210_R1_1_I2,SendRequestVoteAction)
  <1>1. TypeOK /\ Inv210_R1_1_I2 /\ SendRequestVoteAction => Inv210_R1_1_I2'
       BY DEF TypeOK,SendRequestVoteAction,SendRequestVote,Inv210_R1_1_I2
  \* (Inv210_R1_1_I2,SendVoteAction)
  <1>2. TypeOK /\ Inv210_R1_1_I2 /\ SendVoteAction => Inv210_R1_1_I2'
       BY DEF TypeOK,SendVoteAction,SendVote,Inv210_R1_1_I2
  \* (Inv210_R1_1_I2,RecvVoteAction)
  <1>3. TypeOK /\ Inv210_R1_1_I2 /\ RecvVoteAction => Inv210_R1_1_I2'
       BY DEF TypeOK,RecvVoteAction,RecvVote,Inv210_R1_1_I2
  \* (Inv210_R1_1_I2,BecomeLeaderAction)
  <1>4. TypeOK /\ Inv210_R1_1_I2 /\ BecomeLeaderAction => Inv210_R1_1_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv210_R1_1_I2
  \* (Inv210_R1_1_I2,DecideAction)
  <1>5. TypeOK /\ Inv210_R1_1_I2 /\ DecideAction => Inv210_R1_1_I2'
       BY DEF TypeOK,DecideAction,Decide,Inv210_R1_1_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10 DEF Next, IndGlobal






====
