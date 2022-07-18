---- MODULE toy_consensus_IndProofs ----
EXTENDS toy_consensus

\* endive.py stats
\* -----------------
\* date: 2022-08-05T19:37:07.783974
\* is_inductive: True
\* inv_size: 2
\* invcheck_duration_secs: 1.1238219738006592
\* ctielimcheck_duration_secs: 1.4977319240570068
\* ctigen_duration_secs: 3.98393177986145
\* total_duration_secs: 6.611572027206421
\* total_num_ctis_eliminated: 14
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 8
\* total_num_invs_checked: 112
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: False
\* tlc_workers: 8
\* seed: 12
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv78_1_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARV \in Value : \A VARQ \in Quorums : \E VART \in VARQ :(vote[VART] = VARV) \/ (~(VARV \in decision))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv78_1_0_def

ASSUME QuorumType == Quorums \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorums : Q # {}
ASSUME QuorumsExist == Quorums # {}
ASSUME ValueNonEmpty == Value # {}
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME NilType == Nil \notin Node /\ Nil \notin Value


\* TLAPS Proof skeleton.
THEOREM Init => IndAuto
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv78_1_0_def
  <1>2. Inv
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv78_1_0_def
  <1>3. Inv78_1_0_def
    BY QuorumType, QuorumsAreNonEmpty DEF TypeOK,Init,Next,IndAuto,Inv,Inv78_1_0_def
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto, Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv78_1_0_def,CastVote,Decide

  \* Inv == \A vi, vj \in decision : vi = vj
  <1>2. Inv'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv78_1_0_def,CastVote,Decide
    <2>2. CASE \E v \in Value, Q \in Quorums : Decide(v, Q)
        <3>1. PICK v \in Value, Q \in Quorums : Decide(v, Q) BY <2>2
        <3>2. SUFFICES ASSUME NEW vi \in decision',
                              NEW vj \in decision',
                              vi # vj
              PROVE FALSE BY DEF Inv
        <3>3. vi \in decision \/ vj \in decision BY <3>1, <3>2 DEF Decide, IndAuto, TypeOK
        <3>4. CASE vi \in decision
            <4>1. vj = v BY <3>1, <3>2, <3>4 DEF Decide, IndAuto, TypeOK, Inv
            <4>2. ChosenAt(vj, Q) BY <3>1, <4>1 DEF Decide
            <4>3. PICK t \in Q : vote[t] = vi
                BY <3>4, NodeNonEmpty, ValueNonEmpty, QuorumsExist DEF IndAuto, Inv78_1_0_def, TypeOK
            <4>4. vote[t] = vj BY <4>2 DEF ChosenAt
            <4>. QED BY <3>2, <4>3, <4>4 DEF IndAuto, TypeOK
        <3>5. CASE vj \in decision
            <4>1. vi = v BY <3>1, <3>2, <3>4 DEF Decide, IndAuto, TypeOK, Inv
            <4>2. ChosenAt(vi, Q) BY <3>1, <4>1 DEF Decide
            <4>3. PICK t \in Q : vote[t] = vj
                BY <3>5, NodeNonEmpty, ValueNonEmpty, QuorumsExist DEF IndAuto, Inv78_1_0_def, TypeOK
            <4>4. vote[t] = vi BY <4>2 DEF ChosenAt
            <4>. QED BY <3>2, <4>3, <4>4 DEF IndAuto, TypeOK
        <3>. QED BY <3>3, <3>4, <3>5
    <2>3. QED
      BY <2>1, <2>2 DEF Next

  <1>3. Inv78_1_0_def'
    <2>1. CASE \E i \in Node, v \in Value : CastVote(i, v)
        <3>1. PICK i \in Node, v \in Value : CastVote(i, v) BY <2>1
        <3>2. vote[i] # v BY <3>1, NilType DEF CastVote
        <3>3. SUFFICES ASSUME NEW Q \in Quorums',
                              NEW val \in Value,
                              \A t \in Q : (vote'[t] # val) /\ (val \in decision')
              PROVE FALSE
              BY NodeNonEmpty, ValueNonEmpty DEF Inv78_1_0_def
        <3>4. Q \in Quorums BY <3>1, <3>3 DEF CastVote
        <3>5. CASE val # v
            <4>1. \A t \in Q : (vote[t] # val) /\ (val \in decision)
                BY <3>1, <3>3, <3>5, NilType, QuorumType DEF CastVote, IndAuto, TypeOK
            <4>2. ~Inv78_1_0_def BY <3>3, <3>4, <4>1 DEF Inv78_1_0_def
            <4>. QED BY <4>2 DEF IndAuto
        <3>6. CASE val = v
            <4>1. i \notin Q BY <3>1, <3>3, <3>6 DEF CastVote, IndAuto, TypeOK
            <4>2. \A t \in Q : (vote[t] # val) /\ (val \in decision)
                BY <3>1, <3>3, <3>6, <4>1, NilType, QuorumType DEF CastVote, IndAuto, TypeOK
            <4>3. ~Inv78_1_0_def BY <3>3, <3>4, <4>2 DEF Inv78_1_0_def
            <4>. QED BY <4>3 DEF IndAuto
        <3>. QED BY <3>5, <3>6
    <2>2. CASE \E v \in Value, Q \in Quorums : Decide(v, Q)
        <3>1. PICK v \in Value, Q \in Quorums : Decide(v, Q) BY <2>2
        <3>2. \A m \in Q : vote[m] = v BY <3>1 DEF Decide, ChosenAt
        <3>3. \A Qt \in Quorums : \E t \in Qt : vote[t] = v BY <3>2, QuorumsIntersect
        <3>4. SUFFICES ASSUME NEW Qt \in Quorums',
                              NEW val \in Value
              PROVE \E t \in Qt : (vote'[t] = val) \/ (val \notin decision')
              BY NodeNonEmpty, ValueNonEmpty DEF Inv78_1_0_def
        <3>5. \E t \in Qt : vote[t] = v BY <3>3, <3>4
        <3>6. CASE v = val BY <3>1, <3>4, <3>5, <3>6 DEF Decide
        <3>7. CASE v # val
            <4>1. CASE val \notin decision BY <3>1, <3>5, <3>7, <4>1 DEF Decide
            <4>2. CASE val \in decision
                <5>1. \E t \in Q : vote[t] = val
                    BY <3>7, <4>2, NodeNonEmpty, ValueNonEmpty DEF IndAuto, Inv78_1_0_def
                <5>. QED BY <3>2, <3>7, <5>1
            <4>. QED BY <4>1, <4>2
        <3>. QED BY <3>6, <3>7
    <2>3. QED
      BY <2>1, <2>2 DEF Next

  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto

====
