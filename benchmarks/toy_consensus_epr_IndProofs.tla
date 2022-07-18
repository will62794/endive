---- MODULE toy_consensus_epr_IndProofs ----
EXTENDS toy_consensus_epr, FiniteSetTheorems

\* endive.py stats
\* -----------------
\* date: 2022-08-05T19:36:35.009271
\* is_inductive: True
\* inv_size: 4
\* invcheck_duration_secs: 4.827651500701904
\* ctielimcheck_duration_secs: 6.351951360702515
\* ctigen_duration_secs: 5.40147066116333
\* total_duration_secs: 16.597809076309204
\* total_num_ctis_eliminated: 384
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 627
\* total_num_invs_checked: 3260
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
Inv220_1_0_def == \A VARS \in Node : \A VARA \in Value : (VARS \in voted) \/ (~(<<VARS,VARA>> \in vote))
Inv155_1_1_def == \E VARQ \in Quorum : \A VARA \in Value : (ChosenAt(VARQ, VARA)) \/ (~(VARA \in decided))
Inv201_2_2_def == \A VARS \in Node : \A VARA \in Value : \A VARB \in Value : ((VARA = VARB) /\ vote = vote) \/ (~(<<VARS,VARA>> \in vote)) \/ (~(<<VARS,VARB>> \in vote))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv220_1_0_def
  /\ Inv155_1_1_def
  /\ Inv201_2_2_def

ASSUME QuorumType == Quorum \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorum : Q # {}
ASSUME QuorumsExist == Quorum # {}
ASSUME ValueNonEmpty == Value # {}
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def
  <1>2. Safety
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def
  <1>3. Inv220_1_0_def
    BY QuorumsExist, NodeFinite, QuorumType, FS_Subset DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,ChosenAt
  <1>4. Inv155_1_1_def
    BY NodeFinite, QuorumType, QuorumsExist DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,ChosenAt
  <1>5. Inv201_2_2_def
    BY QuorumsExist, NodeFinite, QuorumType, FS_Subset DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,ChosenAt
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto, Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,CastVote,Decide,ChosenAt

  <1>2. Safety'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,CastVote,Decide,ChosenAt
    <2>2. CASE \E v \in Value, Q \in Quorum : Decide(v, Q)
        <3>1. PICK v \in Value, Q \in Quorum : Decide(v, Q) BY <2>2
        <3>2. SUFFICES ASSUME NEW vi \in decided',
                              NEW vj \in decided',
                              vi # vj
              PROVE FALSE BY DEF Safety
        <3>3. vi \in decided \/ vj \in decided BY <3>1, <3>2 DEF Decide, IndAuto, TypeOK
        <3>4. CASE vi \in decided
            <4>1. vj = v BY <3>1, <3>2, <3>4 DEF Decide, IndAuto, TypeOK, Safety
            <4>2. ChosenAt(Q, vj) BY <3>1, <4>1 DEF Decide
            <4>3. PICK Qvi \in Quorum : ChosenAt(Qvi, vi)
                BY <3>4, NodeNonEmpty, ValueNonEmpty DEF IndAuto, Inv155_1_1_def, TypeOK
            <4>4. PICK t \in Node : t \in Q /\ t \in Qvi BY QuorumsIntersect, QuorumType
            <4>5. <<t,vj>> \in vote /\ <<t,vi>> \in vote BY <4>2, <4>3, <4>4 DEF ChosenAt
            <4>. QED BY <3>2, <4>5 DEF IndAuto, Inv201_2_2_def, TypeOK
        <3>5. CASE vj \in decided
            <4>1. vi = v BY <3>1, <3>2, <3>5 DEF Decide, IndAuto, TypeOK, Safety
            <4>2. ChosenAt(Q, vi) BY <3>1, <4>1 DEF Decide
            <4>3. PICK Qvj \in Quorum : ChosenAt(Qvj, vj)
                BY <3>5, NodeNonEmpty, ValueNonEmpty DEF IndAuto, Inv155_1_1_def, TypeOK
            <4>4. PICK t \in Node : t \in Q /\ t \in Qvj BY QuorumsIntersect, QuorumType
            <4>5. <<t,vi>> \in vote /\ <<t,vj>> \in vote BY <4>2, <4>3, <4>4 DEF ChosenAt
            <4>. QED BY <3>2, <4>5 DEF IndAuto, Inv201_2_2_def, TypeOK
        <3>. QED BY <3>3, <3>4, <3>5

    <2>3. QED
      BY <2>1, <2>2 DEF Next
  <1>3. Inv220_1_0_def'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,CastVote,Decide,ChosenAt
    <2>2. CASE \E v \in Value, Q \in Quorum : Decide(v, Q)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,CastVote,Decide,ChosenAt
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  \* Inv155_1_1_def == \E VARQ \in Quorum : \A VARA \in Value : (ChosenAt(VARQ, VARA)) \/ (~(VARA \in decided))
  <1>4. Inv155_1_1_def'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,CastVote,Decide,ChosenAt
    <2>2. CASE \E v \in Value, Q \in Quorum : Decide(v, Q)
        <3>1. PICK v \in Value, Qv \in Quorum : Decide(v, Qv) BY <2>2
        <3>2. SUFFICES ASSUME 
            \A Q \in Quorum : \E vb \in Value : ~ChosenAt(Q, vb)' /\ (vb \in decided')
             PROVE FALSE BY DEF Inv155_1_1_def
        <3>3. PICK va,vb \in Value : (vb \in decided') /\ ~ChosenAt(Qv, vb)' BY <3>1, <3>2
        <3>4. CASE v # vb
            <4>1. vb \in decided BY <3>1, <3>3, <3>4 DEF Decide, IndAuto, TypeOK
            <4>2. ~ChosenAt(Qv, vb) BY <3>1, <3>3, <3>4 DEF Decide, ChosenAt, IndAuto, TypeOK
            <4>3. PICK Q \in Quorum : ChosenAt(Q, vb) BY <4>1 DEF IndAuto, Inv155_1_1_def
            <4>4. PICK n \in Node : n \in Qv /\ n \in Q BY QuorumsIntersect, QuorumType
            <4>5. <<n,vb>> \in vote BY <4>3, <4>4 DEF ChosenAt
            <4>. QED BY <3>1, <3>4, <4>4, <4>5 DEF Decide, ChosenAt, IndAuto, Inv201_2_2_def, TypeOK
        <3>5. CASE v = vb
            <4>1. ~ChosenAt(Qv, v)' BY <3>2, <3>3, <3>5
            <4>. QED BY <3>1, <4>1 DEF Decide, ChosenAt, IndAuto, TypeOK
        <3>. QED BY <3>4, <3>5
    <2>3. QED
      BY <2>1, <2>2 DEF Next

  <1>5. Inv201_2_2_def'
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv220_1_0_def,Inv155_1_1_def,Inv201_2_2_def,CastVote,Decide,ChosenAt
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto

====

