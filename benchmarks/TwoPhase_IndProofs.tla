---- MODULE TwoPhase_IndProofs ----
EXTENDS TwoPhase, FiniteSetTheorems 

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

\* Inductive strengthening conjuncts
Inv276_1_0_def == (tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgs))
Inv45_1_1_def == \A rmi \in RM : ([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "committed"))
Inv79_1_2_def == \A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgs) \/ (~(tmPrepared = tmPrepared \cup {rmi}))
Inv349_1_3_def == \A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgs) \/ (~(rmState[rmi] = "working"))
Inv318_1_4_def == ~([type |-> "Abort"] \in msgs) \/ (~([type |-> "Commit"] \in msgs))
Inv331_1_5_def == ~([type |-> "Abort"] \in msgs) \/ (~(tmState = "init"))
Inv334_1_6_def == \A rmi \in RM : ~([type |-> "Commit"] \in msgs) \/ (~(rmState[rmi] = "aborted"))
Inv344_1_7_def == ~([type |-> "Commit"] \in msgs) \/ (~(tmState = "init"))
Inv1863_2_8_def == \A rmi \in RM : (rmState[rmi] = "prepared") \/ (~([type |-> "Prepared", rm |-> rmi] \in msgs) \/ (~(tmState = "init")))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ TCConsistent
  /\ Inv276_1_0_def
  /\ Inv45_1_1_def
  /\ Inv79_1_2_def
  /\ Inv349_1_3_def
  /\ Inv318_1_4_def
  /\ Inv331_1_5_def
  /\ Inv334_1_6_def
  /\ Inv344_1_7_def
  /\ Inv1863_2_8_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,TCConsistent,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>1. (rmState \in [RM -> {"working", "prepared", "committed", "aborted"}])'
      BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. (tmState \in {"init", "committed", "aborted"})'
      BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. (tmPrepared \in SUBSET RM)'
      <3>1. CASE TMCommit
        BY <3>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>2. CASE TMAbort
        BY <3>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>3. CASE \E rm \in RM : TMRcvPrepared(rm)
        BY <3>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>4. CASE \E rm \in RM : RMPrepare(rm)
        BY <3>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>5. CASE \E rm \in RM : RMChooseToAbort(rm)
        BY <3>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
        BY <3>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
        BY <3>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>8. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next
      
    <2>4. (msgs \in SUBSET Message)'
      <3>1. CASE TMCommit
        BY <3>1 DEF IndAuto, TypeOK, TMCommit, Message
      <3>2. CASE TMAbort
        BY <3>2 DEF IndAuto, TypeOK, TMAbort, Message
      <3>3. CASE \E rm \in RM : TMRcvPrepared(rm)
        BY <3>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>4. CASE \E rm \in RM : RMPrepare(rm)
         <4>.  PICK rmm \in RM : RMPrepare(rmm) BY <3>4
         <4>1. msgs \in SUBSET ([type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}])
             BY DEF IndAuto, TypeOK, Message
         <4>2. {[type |-> "Prepared", rm |-> rmm]} \in SUBSET [type : {"Prepared"}, rm : RM]
             OBVIOUS
         <4>. QED BY <4>1, <4>2 DEF IndAuto, TypeOK, RMPrepare, Message
      <3>5. CASE \E rm \in RM : RMChooseToAbort(rm)
        BY <3>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
        BY <3>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
        BY <3>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
      <3>8. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF Next
      
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF TypeOK
    
  <1>2. TCConsistent'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>3. Inv276_1_0_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>4. Inv45_1_1_def'
    BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
  <1>5. Inv79_1_2_def'
    BY DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
  <1>6. Inv349_1_3_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>7. Inv318_1_4_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>8. Inv331_1_5_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>9. Inv334_1_6_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TMCommit,TypeOK,IndAuto,TCConsistent,
      Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
        <3>1. PICK rm \in RM : RMChooseToAbort(rm) BY <2>5
        <3>2. rmState[rm] = "working" BY <3>1 DEF RMChooseToAbort
        <3>3. ~(tmPrepared = tmPrepared \cup {rm}) BY <3>2 DEF IndAuto, Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
        <3>4. ~([type |-> "Commit"] \in msgs) BY <3>3 DEF IndAuto, Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
        <3>. QED BY <2>5, <3>4 DEF IndAuto, RMChooseToAbort, TypeOK, Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>10. Inv344_1_7_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>11. Inv1863_2_8_def'
    <2>1. CASE TMCommit
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>2. CASE TMAbort
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>3. CASE \E rm \in RM : TMRcvPrepared(rm)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>4. CASE \E rm \in RM : RMPrepare(rm)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>5. CASE \E rm \in RM : RMChooseToAbort(rm)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>6. CASE \E rm \in RM : RMRcvCommitMsg(rm)
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>7. CASE \E rm \in RM : RMRcvAbortMsg(rm)
      BY <2>7 DEF TypeOK,Init,Next,IndAuto,TCConsistent, TMCommit, TMAbort, TMRcvPrepared, RMPrepare, RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg,Inv276_1_0_def,Inv45_1_1_def,Inv79_1_2_def,Inv349_1_3_def,Inv318_1_4_def,Inv331_1_5_def,Inv334_1_6_def,Inv344_1_7_def,Inv1863_2_8_def
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>12. QED
    BY <1>1, <1>10, <1>11, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
====
