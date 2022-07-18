---- MODULE simple_election_IndProofs ----
EXTENDS simple_election,FiniteSetTheorems,TLAPS

\* endive.py stats
\* -----------------
\* date: 2022-08-05T19:34:46.096179
\* is_inductive: True
\* inv_size: 4
\* invcheck_duration_secs: 5.3670713901519775
\* ctielimcheck_duration_secs: 7.457974672317505
\* ctigen_duration_secs: 6.388131380081177
\* total_duration_secs: 19.23183298110962
\* total_num_ctis_eliminated: 551
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 555
\* total_num_invs_checked: 3255
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 12
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv219_1_0_def == \A VARS \in Acceptor : \A VARPA \in Proposer : (VARPA \in start) \/ (~(<<VARS,VARPA>> \in promise))
Inv136_1_1_def == \A VARPA \in Proposer : \E VARQ \in Quorum : (ChosenAt(VARQ,VARPA)) \/ (~(VARPA \in leader))
Inv200_2_2_def == \A VARS \in Acceptor : \A VARPA \in Proposer : \A VARPB \in Proposer : ((VARPA=VARPB) /\ promise = promise) \/ (~(<<VARS,VARPA>> \in promise)) \/ (~(<<VARS,VARPB>> \in promise))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv219_1_0_def
  /\ Inv136_1_1_def
  /\ Inv200_2_2_def


ASSUME QuorumsNonEmpty == Quorum # {}
ASSUME Fin == IsFiniteSet(Acceptor) /\ IsFiniteSet(Proposer)
ASSUME QuorumsType == Quorum \subseteq SUBSET Acceptor
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME NonEmpty == Proposer # {}

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def
  <1>2. Safety
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def
  <1>3. Inv219_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def
  <1>4. Inv136_1_1_def
    BY QuorumsNonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,ChosenAt
  <1>5. Inv200_2_2_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto

 THEOREM IndAuto /\ Next => IndAuto'
   <1> SUFFICES ASSUME IndAuto /\ Next
                PROVE  IndAuto'
     OBVIOUS
   <1>1. TypeOK'
     <2>1. CASE \E p \in Proposer : Send1a(p)
       BY <2>1, QuorumsNonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>2. CASE \E a \in Acceptor, p \in Proposer : Send1b(a, p)
       BY <2>2, QuorumsNonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>3. CASE \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)
       BY <2>3,QuorumsNonEmpty DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF Next

   <1>2. Safety'
     <2>1. CASE \E p \in Proposer : Send1a(p)
       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>2. CASE \E a \in Acceptor, p \in Proposer : Send1b(a, p)
       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>3. CASE \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)
        <3>1. PICK p \in Proposer, Q \in Quorum : Decide(p, Q) BY <2>3
        <3>2. ChosenAt(Q, p) BY <3>1 DEF Decide
        <3>3. SUFFICES ASSUME NEW x \in leader',
                              NEW y \in leader',
                              x # y
              PROVE FALSE BY DEF Safety
        <3>4. x = p \/ y = p BY <3>1, <3>3 DEF Decide, IndAuto, Safety, TypeOK
        <3>5. CASE x = p
            <4>1. y \in leader BY <3>1, <3>3, <3>5 DEF Decide
            <4>2. PICK Qy \in Quorum : ChosenAt(Qy, y) BY <4>1 DEF IndAuto, Inv136_1_1_def, TypeOK
            <4>3. PICK n \in Acceptor : n \in Q /\ n \in Qy BY <3>2, <4>2, QuorumsIntersect, QuorumsType
            <4>4. <<n,p>> \in promise BY <3>1, <3>2, <4>3 DEF ChosenAt
            <4>5. <<n,y>> \in promise BY <4>2, <4>3 DEF ChosenAt
            <4>. QED BY <3>3, <3>5, <4>4, <4>5 DEF IndAuto, Inv200_2_2_def, TypeOK
        <3>6. CASE y = p
            <4>1. x \in leader BY <3>1, <3>3, <3>6 DEF Decide
            <4>2. PICK Qx \in Quorum : ChosenAt(Qx, x) BY <4>1 DEF IndAuto, Inv136_1_1_def, TypeOK
            <4>3. PICK n \in Acceptor : n \in Q /\ n \in Qx BY <3>2, <4>2, QuorumsIntersect, QuorumsType
            <4>4. <<n,p>> \in promise BY <3>1, <3>2, <4>3 DEF ChosenAt
            <4>5. <<n,x>> \in promise BY <4>2, <4>3 DEF ChosenAt
            <4>. QED BY <3>3, <3>6, <4>4, <4>5 DEF IndAuto, Inv200_2_2_def, TypeOK
        <3>. QED BY <3>4, <3>5, <3>6
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF Next

   <1>3. Inv219_1_0_def'
     <2>1. CASE \E p \in Proposer : Send1a(p)
       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>2. CASE \E a \in Acceptor, p \in Proposer : Send1b(a, p)
       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>3. CASE \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)
       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF Next

   <1>4. Inv136_1_1_def'
     <2>1. CASE \E p \in Proposer : Send1a(p)
       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>2. CASE \E a \in Acceptor, p \in Proposer : Send1b(a, p)
       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>3. CASE \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)
       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF Next

   <1>5. Inv200_2_2_def'
     <2>1. CASE \E p \in Proposer : Send1a(p)
       BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>2. CASE \E a \in Acceptor, p \in Proposer : Send1b(a, p)
       BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt,DidNotPromise
     <2>3. CASE \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)
       BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,Inv219_1_0_def,Inv136_1_1_def,Inv200_2_2_def,Send1a,Send1b,Decide,ChosenAt
     <2>4. QED
       BY <2>1, <2>2, <2>3 DEF Next

   <1>6. QED
     BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto

====
