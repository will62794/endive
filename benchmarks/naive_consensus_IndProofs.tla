---- MODULE naive_consensus_IndProofs ----
EXTENDS naive_consensus

\* endive.py stats
\* -----------------
\* date: 2022-08-05T19:32:12.415475
\* is_inductive: True
\* inv_size: 4
\* invcheck_duration_secs: 5.137019872665405
\* ctielimcheck_duration_secs: 15.13862681388855
\* ctigen_duration_secs: 11.058095932006836
\* total_duration_secs: 31.39272975921631
\* total_num_ctis_eliminated: 10000
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 141
\* total_num_invs_checked: 3259
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
Inv255_1_0_def == \A VARA \in Value : (VotedFor(VARA)) \/ (~(VARA \in decision))
Inv1230_2_1_def == \A VARS \in Node : \A VARA \in Value : \A VARQ \in Quorum : (<<VARS,VARA>> \in vote) \/ (~(<<VARQ,VARA>> \in decide) \/ (~(VARS \in VARQ /\ vote = vote)))
Inv217_2_2_def == \A VARS \in Node : \A VARA \in Value : \A VARB \in Value : ((VARA=VARB) /\ vote = vote) \/ (~(<<VARS,VARA>> \in vote) \/ (~(<<VARS,VARB>> \in vote)))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv255_1_0_def
  /\ Inv1230_2_1_def
  /\ Inv217_2_2_def


AXIOM QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
AXIOM QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
AXIOM Nonempty == Node # {} /\ Quorum # {} /\ Value # {}


\* TLAPS Proof skeleton.
THEOREM Init => IndAuto
 BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv255_1_0_def,Inv1230_2_1_def,Inv217_2_2_def

THEOREM IndAuto /\ Next => IndAuto'
    <1>. SUFFICES ASSUME IndAuto, Next
         PROVE IndAuto' OBVIOUS
    <1>1. TypeOK'
        <2>1. CASE \E n \in Node, v \in Value : CastVote(n,v) BY <2>1 DEF CastVote, IndAuto, TypeOK
        <2>2. CASE \E Q \in Quorum, v \in Value : CollectVotes(Q,v) BY <2>2 DEF CollectVotes, IndAuto, TypeOK
        <2>3. CASE \E Q \in Quorum, v \in Value : LearnValue(Q,v) BY <2>3 DEF LearnValue, IndAuto, TypeOK
        <2>. QED BY <2>1, <2>2, <2>3 DEF Next
    <1>2. Safety'
        <2>1. CASE \E n \in Node, v \in Value : CastVote(n,v) BY <2>1 DEF CastVote, IndAuto, TypeOK, Safety
        <2>2. CASE \E Q \in Quorum, v \in Value : CollectVotes(Q,v) BY <2>2 DEF CollectVotes, IndAuto, TypeOK, Safety
        <2>3. CASE \E Q \in Quorum, v \in Value : LearnValue(Q,v)
            <3>1. PICK Q \in Quorum, v \in Value : LearnValue(Q,v) BY <2>3
            <3>2. <<Q,v>> \in decide BY <3>1 DEF LearnValue
            <3>3. \A t \in Q : <<t,v>> \in vote BY <3>1, <3>2, QuorumsAreNodePowersets DEF IndAuto, TypeOK, Inv1230_2_1_def
            <3>4. SUFFICES ASSUME NEW v1 \in Value,
                                  NEW v2 \in Value,
                                  v1 \in decision',
                                  v2 \in decision',
                                  v1 # v2
                  PROVE FALSE BY DEF Safety
            <3>5. v1 \notin decision \/ v2 \notin decision BY <3>1, <3>4 DEF IndAuto, Safety
            <3>6. CASE v1 \notin decision
                <4>1. v = v1 BY <3>1, <3>2, <3>4, <3>6 DEF LearnValue
                <4>2. v2 \in decision BY <3>1, <3>4, <3>6 DEF LearnValue
                \* Inv255_1_0_def == \A s,t \in Node : \A va,vb \in Value : \A Qa \in Quorum : ~(va \in decision) \/ ((VotedFor(va)) /\ (TRUE))
                <4>3. \A s,t \in Node, vb \in Value, Qa \in Quorum : \E Q2 \in Quorum : <<Q2,v2>> \in decide
                    BY <4>2 DEF IndAuto, Inv255_1_0_def, VotedFor
                <4>4. PICK Q2 \in Quorum : <<Q2,v2>> \in decide BY <4>3, Nonempty
                <4>5. PICK n \in Node : n \in Q /\ n \in Q2 BY <3>1, <4>4, QuorumsOverlap, QuorumsAreNodePowersets
                <4>6. <<n,v2>> \in vote BY <4>4, <4>5 DEF IndAuto, TypeOK, Inv1230_2_1_def
                <4>7. <<n,v1>> \in vote BY <3>3, <4>1, <4>5
                <4>. QED BY <3>4, <4>6, <4>7 DEF IndAuto, Inv217_2_2_def
            <3>7. CASE v2 \notin decision
                <4>1. v = v2 BY <3>1, <3>2, <3>4, <3>7 DEF LearnValue
                <4>2. v1 \in decision BY <3>1, <3>4, <3>7 DEF LearnValue
                \* Inv255_1_0_def == \A s,t \in Node : \A va,vb \in Value : \A Qa \in Quorum : ~(va \in decision) \/ ((VotedFor(va)) /\ (TRUE))
                <4>3. \A s,t \in Node, vb \in Value, Qa \in Quorum : \E Q2 \in Quorum : <<Q2,v1>> \in decide
                    BY <4>2 DEF IndAuto, Inv255_1_0_def, VotedFor
                <4>4. PICK Q2 \in Quorum : <<Q2,v1>> \in decide BY <4>3, Nonempty
                <4>5. PICK n \in Node : n \in Q /\ n \in Q2 BY <3>1, <4>4, QuorumsOverlap, QuorumsAreNodePowersets
                <4>6. <<n,v1>> \in vote BY <4>4, <4>5 DEF IndAuto, TypeOK, Inv1230_2_1_def
                <4>7. <<n,v2>> \in vote BY <3>3, <4>1, <4>5
                <4>. QED BY <3>4, <4>6, <4>7 DEF IndAuto, Inv217_2_2_def
            <3>. QED BY <3>5, <3>6, <3>7
        <2>. QED BY <2>1, <2>2, <2>3 DEF Next

    <1>3. Inv255_1_0_def'
        <2>1. CASE \E n \in Node, v \in Value : CastVote(n,v)
            BY <2>1 DEF CastVote, IndAuto, TypeOK, Safety, Inv255_1_0_def, Inv1230_2_1_def, Inv217_2_2_def, VotedFor
        <2>2. CASE \E Q \in Quorum, v \in Value : CollectVotes(Q,v)
            BY <2>2 DEF CollectVotes, IndAuto, TypeOK, Safety, Inv255_1_0_def, Inv1230_2_1_def, Inv217_2_2_def, VotedFor
        <2>3. CASE \E Q \in Quorum, v \in Value : LearnValue(Q,v)
            BY <2>3 DEF LearnValue, IndAuto, TypeOK, Safety, Inv255_1_0_def, Inv1230_2_1_def, Inv217_2_2_def, VotedFor
        <2>. QED BY <2>1, <2>2, <2>3 DEF Next

    <1>4. Inv1230_2_1_def'
        <2>1. CASE \E n \in Node, v \in Value : CastVote(n,v) BY <2>1 DEF CastVote, IndAuto, TypeOK, Inv1230_2_1_def
        <2>2. CASE \E Q \in Quorum, v \in Value : CollectVotes(Q,v)
            BY <2>2, QuorumsOverlap, QuorumsAreNodePowersets DEF CollectVotes, IndAuto, TypeOK, Inv1230_2_1_def
        <2>3. CASE \E Q \in Quorum, v \in Value : LearnValue(Q,v) BY <2>3 DEF LearnValue, IndAuto, TypeOK, Inv1230_2_1_def
        <2>. QED BY <2>1, <2>2, <2>3 DEF Next

    <1>5. Inv217_2_2_def'
        <2>1. CASE \E n \in Node, v \in Value : CastVote(n,v) BY <2>1 DEF CastVote, IndAuto, TypeOK, Inv217_2_2_def
        <2>2. CASE \E Q \in Quorum, v \in Value : CollectVotes(Q,v) BY <2>2 DEF CollectVotes, IndAuto, TypeOK, Inv217_2_2_def
        <2>3. CASE \E Q \in Quorum, v \in Value : LearnValue(Q,v) BY <2>3 DEF LearnValue, IndAuto, TypeOK, Inv217_2_2_def
        <2>. QED BY <2>1, <2>2, <2>3 DEF Next
    <1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto
====

