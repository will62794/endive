---- MODULE TwoPhase_IndProofs ----
EXTENDS TwoPhase 

\* endive.py stats
\* -----------------
\* date: 2022-08-02T23:51:07.734444
\* is_inductive: True
\* inv_size: 10
\* invcheck_duration_secs: 5.525269031524658
\* ctielimcheck_duration_secs: 25.722007274627686
\* ctigen_duration_secs: 9.50075888633728
\* total_duration_secs: 40.838313817977905
\* total_num_ctis_eliminated: 10000
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 1119
\* total_num_invs_checked: 4021
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 11
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* \* Inductive strengthening conjuncts
\* Inv276_1_0_def == (tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgs))
\* Inv45_1_1_def == \A rmi \in RM : ([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "committed"))
\* Inv79_1_2_def == \A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgs) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
\* Inv349_1_3_def == \A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgs) \/ (~(rmState[rmi] = "working"))
\* Inv318_1_4_def == ~([type |-> "Abort"] \in msgs) \/ (~([type |-> "Commit"] \in msgs))
\* Inv331_1_5_def == ~([type |-> "Abort"] \in msgs) \/ (~(tmState = "init"))
\* Inv334_1_6_def == \A rmi \in RM : ~([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "aborted"))
\* Inv344_1_7_def == ~([type |-> "Commit"] \in msgs) \/ (~(tmState = "init"))
\* Inv1863_2_8_def == \A rmi \in RM : (rmState[rmi] = "prepared") \/ (~([type |-> "Prepared", rm |-> rmi] \in msgs) \/ (~(tmState = "init")))

\* \* The inductive invariant candidate.
\* IndAuto ==
\*   /\ TypeOK
\*   /\ TCConsistent
\*   /\ Inv276_1_0_def
\*   /\ Inv45_1_1_def
\*   /\ Inv79_1_2_def
\*   /\ Inv349_1_3_def
\*   /\ Inv318_1_4_def
\*   /\ Inv331_1_5_def
\*   /\ Inv334_1_6_def
\*   /\ Inv344_1_7_def
\*   /\ Inv1863_2_8_def

\* \* TLAPS Proof skeleton.
\* THEOREM Init => IndAuto 
\*  BY DEF TypeOK,Init,Next,IndAuto,TCConsistent,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def

\* THEOREM IndAuto /\ Next => IndAuto'
\*   <1> SUFFICES ASSUME IndAuto /\ Next
\*                PROVE  IndAuto'
\*     OBVIOUS
\*   <1>1. TypeOK'
\*     <2>1. (rmState \in [RM -> {"working", "prepared", "committed", "aborted"}])'
\*       BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. (tmState \in {"init", "committed", "aborted"})'
\*       BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. (tmPrepared \in SUBSET RM)'
\*       <3>1. CASE TMCommit
\*         BY <3>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>2. CASE TMAbort
\*         BY <3>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*         BY <3>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>4. CASE \E rm \in RM : RMPrepare(rm)
\*         BY <3>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*         BY <3>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*         BY <3>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*         BY <3>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>8. QED
\*         BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next
      
\*     <2>4. (msgs \in SUBSET Message)'
\*       <3>1. CASE TMCommit
\*         BY <3>1 DEF IndAuto, TypeOK, TMCommit, Message
\*       <3>2. CASE TMAbort
\*         BY <3>2 DEF IndAuto, TypeOK, TMAbort, Message
\*       <3>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*         BY <3>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>4. CASE \E rm \in RM : RMPrepare(rm)
\*          <4>.  PICK rmm \in RM : RMPrepare(rmm) BY <3>4
\*          <4>1. msgs \in SUBSET ([type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}])
\*              BY DEF IndAuto, TypeOK, Message
\*          <4>2. {[type |-> "Prepared", rm |-> rmm]} \in SUBSET [type : {"Prepared"}, rm : RM]
\*              OBVIOUS
\*          <4>. QED BY <4>1, <4>2 DEF IndAuto, TypeOK, RMPrepare, Message
\*       <3>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*         BY <3>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*         BY <3>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*         BY <3>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*       <3>8. QED
\*         BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next
      
\*     <2>5. QED
\*       BY <2>1, <2>2, <2>3, <2>4 DEF TypeOK
    
\*   <1>2. TCConsistent'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>3. Inv276_1_0_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>4. Inv45_1_1_def'
\*     BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*   <1>5. Inv79_1_2_def'
\*     BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*   <1>6. Inv349_1_3_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>7. Inv318_1_4_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>8. Inv331_1_5_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>9. Inv334_1_6_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TMCommit,TypeOK,IndAuto,TCConsistent,
\*       Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*         <3>1. PICK rm \in RM : RMChooseToAbort(rm) BY <2>5
\*         <3>2. rmState[rm] = "working" BY <3>1 DEF RMChooseToAbort
\*         <3>3. ~(tmPrepared = tmPrepared \cup {rm}) BY <3>2 DEF IndAuto, Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*         <3>4. ~([type |-> "Commit"] \in msgs) BY <3>3 DEF IndAuto, Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*         <3>. QED BY <2>5, <3>4 DEF IndAuto, RMChooseToAbort, TypeOK, Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>10. Inv344_1_7_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>11. Inv1863_2_8_def'
\*     <2>1. CASE TMCommit
\*       BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>2. CASE TMAbort
\*       BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
\*       BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>4. CASE \E rm \in RM : RMPrepare(rm)
\*       BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
\*       BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
\*       BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
\*       BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
\*     <2>8. QED
\*       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
\*   <1>12. QED
\*     BY <1>1, <1>10, <1>11, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto




---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

\* DISCOVERY 2024.


THEOREM (\A i \in RM : rmState[i] \in {"working"}) => (\A i \in RM : rmState[i] \in {"working", "committed"}) OBVIOUS


\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 12
\* num proof obligations: 84
Safety == H_TCConsistent
Inv103_R0_0_I1 == \A VARRMI \in RM : \A VARRMJ \in RM : ~(rmState[VARRMI] = "working") \/ (~(rmState[VARRMJ] = "committed"))
Inv109_R0_1_I1 == \A VARRMI \in RM : ~([type |-> "Abort"] \in msgsAbort) \/ (~(rmState[VARRMI] = "committed"))
Inv108_R0_2_I1 == \A VARRMI \in RM : ~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "aborted"))
Inv111_R1_0_I1 == \A VARRMI \in RM : ~([type |-> "Commit"] \in msgsCommit) \/ (~(rmState[VARRMI] = "working"))
Inv135_R2_0_I1 == ~([type |-> "Abort"] \in msgsAbort) \/ (~([type |-> "Commit"] \in msgsCommit))
Inv227_R2_1_I1 == \A VARRMI \in RM : ~(rmState[VARRMI] = "committed") \/ (~(tmState = "init"))
Inv1302_R3_2_I2 == \A VARRMI \in RM : (rmState[VARRMI] = "prepared") \/ (~(tmState = "init")) \/ (~(tmPrepared = RM))
Inv36_R5_0_I1 == ~([type |-> "Commit"] \in msgsCommit) \/ (~(tmState = "init"))
Inv90_R5_1_I1 == ~([type |-> "Abort"] \in msgsAbort) \/ (~(tmState = "init"))
Inv1786_R7_2_I2 == \A VARRMI \in RM : (rmState[VARRMI] = "prepared") \/ (~(VARRMI \in tmPrepared) \/ (~(tmState = "init")))
Inv1827_R7_2_I2 == \A VARRMI \in RM : (rmState[VARRMI] = "prepared") \/ (~(tmState = "init")) \/ (~([type |-> "Prepared", rm |-> VARRMI] \in msgsPrepared))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv103_R0_0_I1
  /\ Inv111_R1_0_I1
  /\ Inv1302_R3_2_I2
  /\ Inv90_R5_1_I1
  /\ Inv36_R5_0_I1
  /\ Inv1786_R7_2_I2
  /\ Inv1827_R7_2_I2
  /\ Inv109_R0_1_I1
  /\ Inv135_R2_0_I1
  /\ Inv227_R2_1_I1
  /\ Inv108_R0_2_I1


\* mean in-degree: 1.0
\* median in-degree: 1
\* max in-degree: 4
\* min in-degree: 0
\* mean variable slice size: 0


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ TypeOK /\ RMRcvAbortMsgAction => TypeOK'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,TypeOK
  \* (TypeOK,TMAbortAction)
  <1>2. TypeOK /\ TypeOK /\ TMAbortAction => TypeOK'
       BY DEF TypeOK,TMAbortAction,TMAbort,TypeOK
  \* (TypeOK,TMCommitAction)
  <1>3. TypeOK /\ TypeOK /\ TMCommitAction => TypeOK'
       BY DEF TypeOK,TMCommitAction,TMCommit,TypeOK
  \* (TypeOK,TMRcvPreparedAction)
  <1>4. TypeOK /\ TypeOK /\ TMRcvPreparedAction => TypeOK'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,TypeOK
  \* (TypeOK,RMPrepareAction)
  <1>5. TypeOK /\ TypeOK /\ RMPrepareAction => TypeOK'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,TypeOK
  \* (TypeOK,RMChooseToAbortAction)
  <1>6. TypeOK /\ TypeOK /\ RMChooseToAbortAction => TypeOK'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,TypeOK
  \* (TypeOK,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ TypeOK /\ RMRcvCommitMsgAction => TypeOK'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,TypeOK
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv109_R0_1_I1 /\ Inv103_R0_0_I1 /\ Inv108_R0_2_I1 /\ Safety /\ Next => Safety'
  \* (Safety,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv109_R0_1_I1 /\ Safety /\ RMRcvAbortMsgAction => Safety'
       BY DEF TypeOK,Inv109_R0_1_I1,RMRcvAbortMsgAction,RMRcvAbortMsg,Safety,H_TCConsistent
  \* (Safety,TMAbortAction)
  <1>2. TypeOK /\ Safety /\ TMAbortAction => Safety'
       BY DEF TypeOK,TMAbortAction,TMAbort,Safety,H_TCConsistent
  \* (Safety,TMCommitAction)
  <1>3. TypeOK /\ Safety /\ TMCommitAction => Safety'
       BY DEF TypeOK,TMCommitAction,TMCommit,Safety,H_TCConsistent
  \* (Safety,TMRcvPreparedAction)
  <1>4. TypeOK /\ Safety /\ TMRcvPreparedAction => Safety'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Safety,H_TCConsistent
  \* (Safety,RMPrepareAction)
  <1>5. TypeOK /\ Safety /\ RMPrepareAction => Safety'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Safety,H_TCConsistent
  \* (Safety,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv103_R0_0_I1 /\ Safety /\ RMChooseToAbortAction => Safety'
       BY DEF TypeOK,Inv103_R0_0_I1,RMChooseToAbortAction,RMChooseToAbort,Safety,H_TCConsistent
  \* (Safety,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv108_R0_2_I1 /\ Safety /\ RMRcvCommitMsgAction => Safety'
       BY DEF TypeOK,Inv108_R0_2_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Safety,H_TCConsistent
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv103_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv111_R1_0_I1 /\ Inv103_R0_0_I1 /\ Next => Inv103_R0_0_I1'
  \* (Inv103_R0_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv103_R0_0_I1 /\ RMRcvAbortMsgAction => Inv103_R0_0_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv103_R0_0_I1
  \* (Inv103_R0_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv103_R0_0_I1 /\ TMAbortAction => Inv103_R0_0_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv103_R0_0_I1
  \* (Inv103_R0_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv103_R0_0_I1 /\ TMCommitAction => Inv103_R0_0_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv103_R0_0_I1
  \* (Inv103_R0_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv103_R0_0_I1 /\ TMRcvPreparedAction => Inv103_R0_0_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv103_R0_0_I1
  \* (Inv103_R0_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv103_R0_0_I1 /\ RMPrepareAction => Inv103_R0_0_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv103_R0_0_I1
  \* (Inv103_R0_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv103_R0_0_I1 /\ RMChooseToAbortAction => Inv103_R0_0_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv103_R0_0_I1
  \* (Inv103_R0_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv111_R1_0_I1 /\ Inv103_R0_0_I1 /\ RMRcvCommitMsgAction => Inv103_R0_0_I1'
       BY DEF TypeOK,Inv111_R1_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv103_R0_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv111_R1_0_I1
THEOREM L_3 == TypeOK /\ Inv1302_R3_2_I2 /\ Inv111_R1_0_I1 /\ Next => Inv111_R1_0_I1'
  \* (Inv111_R1_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv111_R1_0_I1 /\ RMRcvAbortMsgAction => Inv111_R1_0_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv111_R1_0_I1
  \* (Inv111_R1_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv111_R1_0_I1 /\ TMAbortAction => Inv111_R1_0_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv111_R1_0_I1
  \* (Inv111_R1_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv1302_R3_2_I2 /\ Inv111_R1_0_I1 /\ TMCommitAction => Inv111_R1_0_I1'
       BY DEF TypeOK,Inv1302_R3_2_I2,TMCommitAction,TMCommit,Inv111_R1_0_I1
  \* (Inv111_R1_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv111_R1_0_I1 /\ TMRcvPreparedAction => Inv111_R1_0_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv111_R1_0_I1
  \* (Inv111_R1_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv111_R1_0_I1 /\ RMPrepareAction => Inv111_R1_0_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv111_R1_0_I1
  \* (Inv111_R1_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv111_R1_0_I1 /\ RMChooseToAbortAction => Inv111_R1_0_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv111_R1_0_I1
  \* (Inv111_R1_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv111_R1_0_I1 /\ RMRcvCommitMsgAction => Inv111_R1_0_I1'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv111_R1_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv1302_R3_2_I2
THEOREM L_4 == TypeOK /\ Inv90_R5_1_I1 /\ Inv1786_R7_2_I2 /\ Inv1827_R7_2_I2 /\ Inv36_R5_0_I1 /\ Inv1302_R3_2_I2 /\ Next => Inv1302_R3_2_I2'
  \* (Inv1302_R3_2_I2,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv90_R5_1_I1 /\ Inv1302_R3_2_I2 /\ RMRcvAbortMsgAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,Inv90_R5_1_I1,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1302_R3_2_I2
  \* (Inv1302_R3_2_I2,TMAbortAction)
  <1>2. TypeOK /\ Inv1302_R3_2_I2 /\ TMAbortAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv1302_R3_2_I2
  \* (Inv1302_R3_2_I2,TMCommitAction)
  <1>3. TypeOK /\ Inv1302_R3_2_I2 /\ TMCommitAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv1302_R3_2_I2
  \* (Inv1302_R3_2_I2,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1786_R7_2_I2 /\ Inv1827_R7_2_I2 /\ Inv1302_R3_2_I2 /\ TMRcvPreparedAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,Inv1786_R7_2_I2,Inv1827_R7_2_I2,TMRcvPreparedAction,TMRcvPrepared,Inv1302_R3_2_I2
  \* (Inv1302_R3_2_I2,RMPrepareAction)
  <1>5. TypeOK /\ Inv1302_R3_2_I2 /\ RMPrepareAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1302_R3_2_I2
  \* (Inv1302_R3_2_I2,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1302_R3_2_I2 /\ RMChooseToAbortAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1302_R3_2_I2
  \* (Inv1302_R3_2_I2,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv36_R5_0_I1 /\ Inv1302_R3_2_I2 /\ RMRcvCommitMsgAction => Inv1302_R3_2_I2'
       BY DEF TypeOK,Inv36_R5_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1302_R3_2_I2
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv90_R5_1_I1
THEOREM L_5 == TypeOK /\ Inv90_R5_1_I1 /\ Next => Inv90_R5_1_I1'
  \* (Inv90_R5_1_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv90_R5_1_I1 /\ RMRcvAbortMsgAction => Inv90_R5_1_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv90_R5_1_I1
  \* (Inv90_R5_1_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv90_R5_1_I1 /\ TMAbortAction => Inv90_R5_1_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv90_R5_1_I1
  \* (Inv90_R5_1_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv90_R5_1_I1 /\ TMCommitAction => Inv90_R5_1_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv90_R5_1_I1
  \* (Inv90_R5_1_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv90_R5_1_I1 /\ TMRcvPreparedAction => Inv90_R5_1_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv90_R5_1_I1
  \* (Inv90_R5_1_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv90_R5_1_I1 /\ RMPrepareAction => Inv90_R5_1_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv90_R5_1_I1
  \* (Inv90_R5_1_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv90_R5_1_I1 /\ RMChooseToAbortAction => Inv90_R5_1_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv90_R5_1_I1
  \* (Inv90_R5_1_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv90_R5_1_I1 /\ RMRcvCommitMsgAction => Inv90_R5_1_I1'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv90_R5_1_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv36_R5_0_I1
THEOREM L_6 == TypeOK /\ Inv36_R5_0_I1 /\ Next => Inv36_R5_0_I1'
  \* (Inv36_R5_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv36_R5_0_I1 /\ RMRcvAbortMsgAction => Inv36_R5_0_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv36_R5_0_I1
  \* (Inv36_R5_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv36_R5_0_I1 /\ TMAbortAction => Inv36_R5_0_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv36_R5_0_I1
  \* (Inv36_R5_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv36_R5_0_I1 /\ TMCommitAction => Inv36_R5_0_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv36_R5_0_I1
  \* (Inv36_R5_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv36_R5_0_I1 /\ TMRcvPreparedAction => Inv36_R5_0_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv36_R5_0_I1
  \* (Inv36_R5_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv36_R5_0_I1 /\ RMPrepareAction => Inv36_R5_0_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv36_R5_0_I1
  \* (Inv36_R5_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv36_R5_0_I1 /\ RMChooseToAbortAction => Inv36_R5_0_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv36_R5_0_I1
  \* (Inv36_R5_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv36_R5_0_I1 /\ RMRcvCommitMsgAction => Inv36_R5_0_I1'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv36_R5_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next

\*ASSUME Fin == RM = {0,1,2}
\*USE Fin

\*** Inv1786_R7_2_I2
THEOREM L_7 == TypeOK /\ Inv1827_R7_2_I2 /\ Inv1786_R7_2_I2 /\ Next => Inv1786_R7_2_I2'
  \* (Inv1786_R7_2_I2,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv1786_R7_2_I2 /\ RMRcvAbortMsgAction => Inv1786_R7_2_I2'
    BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1786_R7_2_I2
       
  \* (Inv1786_R7_2_I2,TMAbortAction)
  <1>2. TypeOK /\ Inv1786_R7_2_I2 /\ TMAbortAction => Inv1786_R7_2_I2'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv1786_R7_2_I2
  \* (Inv1786_R7_2_I2,TMCommitAction)
  <1>3. TypeOK /\ Inv1786_R7_2_I2 /\ TMCommitAction => Inv1786_R7_2_I2'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv1786_R7_2_I2
  \* (Inv1786_R7_2_I2,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1827_R7_2_I2 /\ Inv1786_R7_2_I2 /\ TMRcvPreparedAction => Inv1786_R7_2_I2'
       BY DEF TypeOK,Inv1827_R7_2_I2,TMRcvPreparedAction,TMRcvPrepared,Inv1786_R7_2_I2
  \* (Inv1786_R7_2_I2,RMPrepareAction)
  <1>5. TypeOK /\ Inv1786_R7_2_I2 /\ RMPrepareAction => Inv1786_R7_2_I2'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1786_R7_2_I2
  \* (Inv1786_R7_2_I2,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1786_R7_2_I2 /\ RMChooseToAbortAction => Inv1786_R7_2_I2'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1786_R7_2_I2
  \* (Inv1786_R7_2_I2,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv1786_R7_2_I2 /\ RMRcvCommitMsgAction => Inv1786_R7_2_I2'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1786_R7_2_I2
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv1827_R7_2_I2
THEOREM L_8 == TypeOK /\ Inv1827_R7_2_I2 /\ Next => Inv1827_R7_2_I2'
  \* (Inv1827_R7_2_I2,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv1827_R7_2_I2 /\ RMRcvAbortMsgAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv1827_R7_2_I2
  \* (Inv1827_R7_2_I2,TMAbortAction)
  <1>2. TypeOK /\ Inv1827_R7_2_I2 /\ TMAbortAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv1827_R7_2_I2
  \* (Inv1827_R7_2_I2,TMCommitAction)
  <1>3. TypeOK /\ Inv1827_R7_2_I2 /\ TMCommitAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv1827_R7_2_I2
  \* (Inv1827_R7_2_I2,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv1827_R7_2_I2 /\ TMRcvPreparedAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv1827_R7_2_I2
  \* (Inv1827_R7_2_I2,RMPrepareAction)
  <1>5. TypeOK /\ Inv1827_R7_2_I2 /\ RMPrepareAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv1827_R7_2_I2
  \* (Inv1827_R7_2_I2,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv1827_R7_2_I2 /\ RMChooseToAbortAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv1827_R7_2_I2
  \* (Inv1827_R7_2_I2,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv1827_R7_2_I2 /\ RMRcvCommitMsgAction => Inv1827_R7_2_I2'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv1827_R7_2_I2
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv109_R0_1_I1
THEOREM L_9 == TypeOK /\ Inv227_R2_1_I1 /\ Inv135_R2_0_I1 /\ Inv109_R0_1_I1 /\ Next => Inv109_R0_1_I1'
  \* (Inv109_R0_1_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv109_R0_1_I1 /\ RMRcvAbortMsgAction => Inv109_R0_1_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv109_R0_1_I1
  \* (Inv109_R0_1_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv227_R2_1_I1 /\ Inv109_R0_1_I1 /\ TMAbortAction => Inv109_R0_1_I1'
       BY DEF TypeOK,Inv227_R2_1_I1,TMAbortAction,TMAbort,Inv109_R0_1_I1
  \* (Inv109_R0_1_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv109_R0_1_I1 /\ TMCommitAction => Inv109_R0_1_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv109_R0_1_I1
  \* (Inv109_R0_1_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv109_R0_1_I1 /\ TMRcvPreparedAction => Inv109_R0_1_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv109_R0_1_I1
  \* (Inv109_R0_1_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv109_R0_1_I1 /\ RMPrepareAction => Inv109_R0_1_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv109_R0_1_I1
  \* (Inv109_R0_1_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv109_R0_1_I1 /\ RMChooseToAbortAction => Inv109_R0_1_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv109_R0_1_I1
  \* (Inv109_R0_1_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv135_R2_0_I1 /\ Inv109_R0_1_I1 /\ RMRcvCommitMsgAction => Inv109_R0_1_I1'
       BY DEF TypeOK,Inv135_R2_0_I1,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv109_R0_1_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv135_R2_0_I1
THEOREM L_10 == TypeOK /\ Inv135_R2_0_I1 /\ Next => Inv135_R2_0_I1'
  \* (Inv135_R2_0_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv135_R2_0_I1 /\ RMRcvAbortMsgAction => Inv135_R2_0_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv135_R2_0_I1
  \* (Inv135_R2_0_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv135_R2_0_I1 /\ TMAbortAction => Inv135_R2_0_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv135_R2_0_I1
  \* (Inv135_R2_0_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv135_R2_0_I1 /\ TMCommitAction => Inv135_R2_0_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv135_R2_0_I1
  \* (Inv135_R2_0_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv135_R2_0_I1 /\ TMRcvPreparedAction => Inv135_R2_0_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv135_R2_0_I1
  \* (Inv135_R2_0_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv135_R2_0_I1 /\ RMPrepareAction => Inv135_R2_0_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv135_R2_0_I1
  \* (Inv135_R2_0_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv135_R2_0_I1 /\ RMChooseToAbortAction => Inv135_R2_0_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv135_R2_0_I1
  \* (Inv135_R2_0_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv135_R2_0_I1 /\ RMRcvCommitMsgAction => Inv135_R2_0_I1'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv135_R2_0_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv227_R2_1_I1
THEOREM L_11 == TypeOK /\ Inv227_R2_1_I1 /\ Next => Inv227_R2_1_I1'
  \* (Inv227_R2_1_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv227_R2_1_I1 /\ RMRcvAbortMsgAction => Inv227_R2_1_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv227_R2_1_I1
  \* (Inv227_R2_1_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv227_R2_1_I1 /\ TMAbortAction => Inv227_R2_1_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv227_R2_1_I1
  \* (Inv227_R2_1_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv227_R2_1_I1 /\ TMCommitAction => Inv227_R2_1_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv227_R2_1_I1
  \* (Inv227_R2_1_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv227_R2_1_I1 /\ TMRcvPreparedAction => Inv227_R2_1_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv227_R2_1_I1
  \* (Inv227_R2_1_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv227_R2_1_I1 /\ RMPrepareAction => Inv227_R2_1_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv227_R2_1_I1
  \* (Inv227_R2_1_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv227_R2_1_I1 /\ RMChooseToAbortAction => Inv227_R2_1_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv227_R2_1_I1
  \* (Inv227_R2_1_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv227_R2_1_I1 /\ RMRcvCommitMsgAction => Inv227_R2_1_I1'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv227_R2_1_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


\*** Inv108_R0_2_I1
THEOREM L_12 == TypeOK /\ Inv108_R0_2_I1 /\ Next => Inv108_R0_2_I1'
  \* (Inv108_R0_2_I1,RMRcvAbortMsgAction)
  <1>1. TypeOK /\ Inv108_R0_2_I1 /\ RMRcvAbortMsgAction => Inv108_R0_2_I1'
       BY DEF TypeOK,RMRcvAbortMsgAction,RMRcvAbortMsg,Inv108_R0_2_I1
  \* (Inv108_R0_2_I1,TMAbortAction)
  <1>2. TypeOK /\ Inv108_R0_2_I1 /\ TMAbortAction => Inv108_R0_2_I1'
       BY DEF TypeOK,TMAbortAction,TMAbort,Inv108_R0_2_I1
  \* (Inv108_R0_2_I1,TMCommitAction)
  <1>3. TypeOK /\ Inv108_R0_2_I1 /\ TMCommitAction => Inv108_R0_2_I1'
       BY DEF TypeOK,TMCommitAction,TMCommit,Inv108_R0_2_I1
  \* (Inv108_R0_2_I1,TMRcvPreparedAction)
  <1>4. TypeOK /\ Inv108_R0_2_I1 /\ TMRcvPreparedAction => Inv108_R0_2_I1'
       BY DEF TypeOK,TMRcvPreparedAction,TMRcvPrepared,Inv108_R0_2_I1
  \* (Inv108_R0_2_I1,RMPrepareAction)
  <1>5. TypeOK /\ Inv108_R0_2_I1 /\ RMPrepareAction => Inv108_R0_2_I1'
       BY DEF TypeOK,RMPrepareAction,RMPrepare,Inv108_R0_2_I1
  \* (Inv108_R0_2_I1,RMChooseToAbortAction)
  <1>6. TypeOK /\ Inv108_R0_2_I1 /\ RMChooseToAbortAction => Inv108_R0_2_I1'
       BY DEF TypeOK,RMChooseToAbortAction,RMChooseToAbort,Inv108_R0_2_I1
  \* (Inv108_R0_2_I1,RMRcvCommitMsgAction)
  <1>7. TypeOK /\ Inv108_R0_2_I1 /\ RMRcvCommitMsgAction => Inv108_R0_2_I1'
       BY DEF TypeOK,RMRcvCommitMsgAction,RMRcvCommitMsg,Inv108_R0_2_I1
<1>8. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12 DEF Next, IndGlobal


====
