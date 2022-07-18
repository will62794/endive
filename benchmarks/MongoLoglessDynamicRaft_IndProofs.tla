---- MODULE MongoLoglessDynamicRaft_IndProofs ----
EXTENDS TLC, MongoLoglessDynamicRaft, FiniteSetTheorems

\* endive.py stats
\* -----------------
\* date: 2022-08-13T21:44:50.485205
\* is_inductive: True
\* inv_size: 6
\* invcheck_duration_secs: 0
\* ctielimcheck_duration_secs: 652.8699855804443
\* ctigen_duration_secs: 102.15992975234985
\* total_duration_secs: 755.3718907833099
\* total_num_ctis_eliminated: 7751
\* total_num_cti_elimination_rounds: 3
\* total_num_invs_generated: 7006
\* total_num_invs_checked: 7006
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 24
\* seed: 12
\* os: posix
\* system: Linux
\* java_exe: java -Xss4M
\* java_version_info: openjdk version "11.0.12" 2021-07-20 LTS OpenJDK Runtime Environment 18.9 (build 11.0.12+7-LTS) OpenJDK 64-Bit Server VM 18.9 (build 11.0.12+7-LTS, mixed mode, sharing)
\* processor: x86_64
\* cpu_count: 48

\* Inductive strengthening conjuncts
Inv2973_1_1_def == \A i,j \in Server : (QuorumsOverlap(config[i], config[j])) \/ ((ConfigDisabled(i)) \/ ((ConfigDisabled(j)) /\ (TRUE)))
Inv1758_1_0_def == \A i,j \in Server : ((config[i] = config[j])) \/ ((IsNewerConfig(j, i)) \/ ((IsNewerConfig(i, j)) /\ (TRUE)))
Inv3915_1_1_def == \A i,j \in Server : ~((configTerm[i] = configTerm[j])) \/ (~((state[i] = Primary)) \/ (~(IsNewerConfig(j, i)) /\ (TRUE)))
Inv3246_1_2_def == \A i,j \in Server : \A Q \in Quorums(config[j]) : \E n \in Q : ((currentTerm[n] >= configTerm[i])) \/ ((ConfigDisabled(j)))
Inv866_1_0_def == \A i,j \in Server : ((configTerm[j] = currentTerm[j])) \/ (~((state[j] = Primary)) /\ (TRUE))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv2973_1_1_def
  /\ Inv1758_1_0_def
  /\ Inv3915_1_1_def
  /\ Inv3246_1_2_def
  /\ Inv866_1_0_def
  
  
  


ActiveConfigSet == {s \in Server : ~ConfigDisabled(s)}
  
Inv862_1_0_def == TRUE
Inv846_1_0_def == TRUE
Inv6243_1_1_def == TRUE
Inv648_1_0_def == TRUE
Inv1925_1_1_def == TRUE
Inv716_1_1_def == TRUE
Inv852_1_2_def == TRUE
\*IndAuto == TRUE


ASSUME PrimaryAndSecondaryAreDifferent == Primary # Secondary
ASSUME ServerIsFinite == IsFiniteSet(Server)
ASSUME ServerIsNonempty == Server # {}


LEMMA QuorumsOverlapIsCommutative ==
ASSUME TypeOK
PROVE \A conf1,conf2 \in SUBSET Server :
        QuorumsOverlap(conf1,conf2) <=> QuorumsOverlap(conf2,conf1)
PROOF
    <1>1. TAKE conf1, conf2 \in SUBSET Server
    <1>2. QuorumsOverlap(conf1,conf2) => QuorumsOverlap(conf2,conf1)
        <2>1. SUFFICES ASSUME QuorumsOverlap(conf1,conf2)
              PROVE QuorumsOverlap(conf2,conf1) OBVIOUS
        <2>2. \A qx \in Quorums(conf1), qy \in Quorums(conf2) : qx \cap qy # {} BY <2>1 DEF QuorumsOverlap
        <2>3. \A qy \in Quorums(conf2), qx \in Quorums(conf1) : qy \cap qx # {} BY <2>2
        <2>. QED BY <2>3 DEF QuorumsOverlap
    <1>3. QuorumsOverlap(conf2,conf1) => QuorumsOverlap(conf1,conf2)
        <2>1. SUFFICES ASSUME QuorumsOverlap(conf2,conf1)
              PROVE QuorumsOverlap(conf1,conf2) OBVIOUS
        <2>2. \A qx \in Quorums(conf2), qy \in Quorums(conf1) : qx \cap qy # {} BY <2>1 DEF QuorumsOverlap
        <2>3. \A qy \in Quorums(conf1), qx \in Quorums(conf2) : qy \cap qx # {} BY <2>2
        <2>. QED BY <2>3 DEF QuorumsOverlap
    <1>. QED BY <1>2, <1>3


LEMMA QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorums(S) # {}
PROOF BY FS_EmptySet, FS_CardinalityType DEF Quorums

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE Quorums(config[s]) \subseteq SUBSET Server
PROOF BY DEF Quorums, TypeOK

LEMMA StaticQuorumsOverlap ==
ASSUME NEW cfg \in SUBSET Server,
       NEW Q1 \in Quorums(cfg),
       NEW Q2 \in Quorums(cfg)
PROVE Q1 \cap Q2 # {}
PROOF
    <1>. IsFiniteSet(cfg)
        BY FS_Subset, ServerIsFinite
    <1>. IsFiniteSet(Q1) /\ IsFiniteSet(Q2)
        BY QuorumsAreServerSubsets, ServerIsFinite, FS_Subset DEF Quorums
    <1>. IsFiniteSet(Q1 \cap Q2)
        BY FS_Intersection
    <1>1. Q1 \in SUBSET cfg /\ Q2 \in SUBSET cfg
        BY QuorumsAreServerSubsets DEF Quorums, TypeOK
    <1>2. Cardinality(Q1) + Cardinality(Q2) <= Cardinality(cfg) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1 \cup Q2) = Cardinality(Q1) + Cardinality(Q2) - Cardinality(Q1 \cap Q2)
            BY FS_Union
        <2>2. Cardinality(Q1 \cup Q2) <= Cardinality(cfg)
            BY <1>1, FS_Subset, ServerIsFinite
        <2>3. QED BY <2>1, <2>2, FS_CardinalityType
    <1>3. Cardinality(Q1) + Cardinality(Q2) < Cardinality(Q1) + Cardinality(Q2) + Cardinality(Q1 \cap Q2)
        <2>1. Cardinality(Q1) * 2 > Cardinality(cfg) /\ Cardinality(Q2) * 2 > Cardinality(cfg)
            BY <1>1 DEF Quorums, TypeOK
        <2>2. Cardinality(Q1) + Cardinality(Q2) > Cardinality(cfg)
            BY <2>1, FS_CardinalityType, ServerIsFinite
        <2>3. QED BY <2>2, <1>2, FS_CardinalityType
    <1>4. Cardinality(Q1 \cap Q2) > 0
        BY <1>3, FS_CardinalityType
    <1>5. QED BY <1>4, FS_EmptySet

COROLLARY ConfigQuorumsOverlap ==
ASSUME NEW cfg \in SUBSET Server
PROVE QuorumsOverlap(cfg, cfg)
PROOF BY StaticQuorumsOverlap DEF QuorumsOverlap

LEMMA QuorumsAreNonEmpty ==
ASSUME \/ config \in [Server -> SUBSET Server]
       \/ TypeOK,
       NEW s \in Server
PROVE \A Q \in Quorums(config[s]) : Q # {}
PROOF
    <1>. config \in [Server -> SUBSET Server] BY DEF TypeOK
    <1>. SUFFICES ASSUME \E Q \in Quorums(config[s]) : Q = {}
         PROVE FALSE OBVIOUS
    <1>. PICK Q \in Quorums(config[s]) : Q = {} OBVIOUS
    <1>1. Cardinality(Q) * 2 = 0
        <2>1. Cardinality(Q) = 0 BY FS_EmptySet
        <2>. QED BY <2>1, FS_CardinalityType
    <1>2. Cardinality(Q) * 2 > 0
        <2>1. Cardinality(config[s]) >= 0 /\ IsFiniteSet(config[s])
            BY ServerIsFinite, FS_CardinalityType, FS_Subset DEF Quorums
        <2>2. Cardinality(Q) * 2 > Cardinality(config[s]) BY <2>1, FS_CardinalityType DEF Quorums
        <2>3. IsFiniteSet(Q) BY ServerIsFinite, FS_Subset DEF Quorums
        <2>. QED BY <2>1, <2>2, <2>3, FS_CardinalityType
    <1>. QED BY <1>1, <1>2

ASSUME InitTermType == InitTerm \in Nat


LEMMA NewerOrEqualConfigEquivalence ==
ASSUME NEW s \in Server,
       NEW t \in Server
PROVE IsNewerOrEqualConfig(s, t) <=> NewerOrEqualConfig(CV(s), CV(t))
BY DEF IsNewerConfig, NewerConfig, IsNewerOrEqualConfig, NewerOrEqualConfig, CV

LEMMA NewerIsNotSymmetric ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server
PROVE /\ IsNewerConfig(s, t) <=> ~IsNewerOrEqualConfig(t, s)
      /\ NewerConfig(CV(s), CV(t)) <=> ~NewerOrEqualConfig(CV(t), CV(s))
BY DEF IsNewerConfig, IsNewerOrEqualConfig, NewerConfig, NewerOrEqualConfig, CV, TypeOK

LEMMA ElectedLeadersInActiveConfigSet ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       BecomeLeader(s, Q)
PROVE s \in ActiveConfigSet
PROOF
    <1>1. \A v \in Q : IsNewerOrEqualConfig(s, v) BY DEF BecomeLeader, CanVoteForConfig
    <1>2. \A v \in Q : NewerOrEqualConfig(CV(s), CV(v)) BY <1>1, NewerOrEqualConfigEquivalence DEF Quorums, TypeOK
    <1>3. \A v \in Q : ~NewerConfig(CV(v), CV(s)) BY <1>2, NewerIsNotSymmetric DEF Quorums, TypeOK
    <1>. QED BY <1>3 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK

LEMMA ElectedLeadersCurrentTermGreaterThanConfigTerms ==
ASSUME IndAuto,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       BecomeLeader(s, Q)
PROVE \A t \in Server : currentTerm[s] >= configTerm[t]
PROOF
    <1>. TAKE t \in Server
    <1>1. PICK n \in Q : currentTerm[n] >= configTerm[t] 
        BY ElectedLeadersInActiveConfigSet 
        DEF IndAuto, Inv1758_1_0_def, ActiveConfigSet, Inv3246_1_2_def
    <1>2. currentTerm[s] >= currentTerm[n] 
        BY <1>1 
        DEF BecomeLeader, CanVoteForConfig, Quorums, IndAuto, TypeOK
    <1>. QED BY <1>1, <1>2 DEF Quorums, IndAuto, TypeOK

LEMMA TypeOKAndNext ==
ASSUME TypeOK, Next
PROVE TypeOK'
PROOF
   <1>1. QED BY DEF TypeOK,Init,Next,Safety,
      Inv2973_1_1_def,Inv2973_1_1_def,Inv2973_1_1_def,Inv2973_1_1_def,Inv2973_1_1_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms,UpdateTermsExpr,
      ReconfigAction,SendConfigAction,BecomeLeaderAction,UpdateTermsAction

LEMMA ConfigVersionAndTermUniqueAndNext_BecomeLeader ==
ASSUME IndAuto, Next,
       NEW s \in Server,
       NEW Q \in Quorums(config[s]),
       BecomeLeader(s, Q),
       BecomeLeader(s, Q),
       NEW t \in Server,
       <<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>
PROVE config'[s] = config'[t]
PROOF
    <1>ok. TypeOK BY DEF IndAuto
    <1>1. \A n \in Server : currentTerm[s] >= configTerm[n] BY ElectedLeadersCurrentTermGreaterThanConfigTerms DEF IndAuto
    <1>. QED BY <1>ok, <1>1, TypeOKAndNext DEF BecomeLeader, TypeOK

LEMMA NewerConfigEquivalence ==
ASSUME NEW s \in Server,
       NEW t \in Server
PROVE IsNewerConfig(s, t) <=> NewerConfig(CV(s), CV(t))
BY DEF IsNewerConfig, NewerConfig, CV

LEMMA ReconfigImpliesConfigTermUnchanged ==
ASSUME IndAuto,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(s, newConfig)
PROVE \A t \in Server : configTerm'[t] = configTerm[t] /\ currentTerm'[t] = currentTerm[t]
PROOF
    <1>1. state[s] = Primary BY DEF Reconfig
    <1>2. configTerm[s] = currentTerm[s] BY <1>1 DEF IndAuto, Inv1758_1_0_def,Inv3246_1_2_def, Inv866_1_0_def
    <1>. QED BY <1>2 DEF Reconfig, TypeOK

LEMMA SendConfigImpliesNewerOrEqualConfig ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       SendConfig(s, t)
PROVE /\ NewerConfig(CV(t)', CV(t))
      /\ \A u \in Server : u # t => CV(u)' = CV(u)
      /\ \A u \in Server : NewerOrEqualConfig(CV(u)', CV(u))
PROOF
    <1>1. NewerConfig(CV(t)', CV(t))
        <2>1. NewerConfig(CV(s), CV(t)) BY NewerConfigEquivalence DEF SendConfig, TypeOK
        <2>. QED BY <2>1 DEF SendConfig, NewerConfig, CV, TypeOK
    <1>2. \A u \in Server : u # t => CV(u)' = CV(u) BY DEF SendConfig, CV, TypeOK
    <1>3. \A u \in Server : NewerOrEqualConfig(CV(u)', CV(u)) BY <1>1, <1>2 DEF NewerOrEqualConfig, NewerConfig, CV, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3

LEMMA ReconfigImpliesNewerOrEqualConfig ==
ASSUME IndAuto,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(s, newConfig)
PROVE /\ NewerConfig(CV(s)', CV(s))
      /\ \A t \in Server : t # s => CV(t)' = CV(t)
      /\ \A t \in Server : NewerOrEqualConfig(CV(t)', CV(t))
PROOF
    <1>1. NewerConfig(CV(s)', CV(s))
        <2>1. configVersion'[s] > configVersion[s] BY DEF Reconfig, IndAuto, TypeOK
        <2>. QED BY <2>1, ReconfigImpliesConfigTermUnchanged DEF NewerConfig, CV
    <1>2. \A t \in Server : t # s => CV(t)' = CV(t) BY DEF Reconfig, CV
    <1>3. \A t \in Server : NewerOrEqualConfig(CV(t)', CV(t)) BY <1>1, <1>2 DEF NewerOrEqualConfig, NewerConfig, CV
    <1>. QED BY <1>1, <1>2, <1>3

LEMMA ConfigsIncreaseMonotonically ==
ASSUME IndAuto, Next
PROVE \A s \in Server : NewerOrEqualConfig(CV(s)', CV(s))
    <1>ok. TypeOK BY DEF IndAuto
    <1>1. CASE \E s \in Server, newConfig \in SUBSET Server : Reconfig(s, newConfig)
        BY <1>ok, <1>1, ReconfigImpliesNewerOrEqualConfig
    <1>2. CASE \E s,t \in Server : SendConfig(s, t)
        BY <1>ok, <1>2, SendConfigImpliesNewerOrEqualConfig
    <1>3. CASE \E s \in Server : \E Q \in Quorums(config[s]) : BecomeLeader(s, Q) /\ BecomeLeader(s, Q)
        <3>1. PICK s \in Server : \E Q \in Quorums(config[s]) : BecomeLeader(s, Q) /\ BecomeLeader(s, Q) BY <1>3
        <3>2. \A t \in Server : t # s => CV(t)' = CV(t) BY <3>1 DEF BecomeLeader, CV, TypeOK
        <3>3. NewerConfig(CV(s)', CV(s))
            <4>1. currentTerm[s] >= configTerm[s] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms
            <4>2. configTerm'[s] > configTerm[s] BY <1>ok, <3>1, <4>1 DEF BecomeLeader, TypeOK
            <4>3. configVersion'[s] = configVersion[s] BY <3>1 DEF BecomeLeader
            <4>. QED BY <4>2, <4>3 DEF NewerConfig, CV, TypeOK
        <3>. QED BY <3>2, <3>3 DEF NewerOrEqualConfig
    <1>4. CASE \E s,t \in Server : UpdateTerms(s,t) /\ UpdateTerms(s,t)
        BY <1>4 DEF UpdateTerms, NewerOrEqualConfig, NewerConfig, CV, TypeOK
    <1>. QED BY <1>1, <1>2, <1>3,<1>4  
         DEF Next, ReconfigAction, SendConfigAction, BecomeLeaderAction, UpdateTermsAction

LEMMA NewerOrEqualConfigTransitivityAndNext ==
ASSUME TypeOK, Next,
       NEW s \in Server,
       NEW t \in Server,
       NEW u \in Server,
       NewerOrEqualConfig(CV(s)', CV(t)'),
       NewerOrEqualConfig(CV(t)', CV(u))
PROVE NewerOrEqualConfig(CV(s)', CV(u))
PROOF BY TypeOKAndNext DEF NewerOrEqualConfig, NewerConfig, CV, TypeOK

LEMMA NewerIsNotSymmetricAndNext ==
ASSUME TypeOK, Next,
       NEW s \in Server,
       NEW t \in Server
PROVE /\ IsNewerConfig(s, t)' <=> ~IsNewerOrEqualConfig(t, s)'
      /\ NewerConfig(CV(s), CV(t))' <=> ~NewerOrEqualConfig(CV(t), CV(s))'
BY TypeOKAndNext DEF IsNewerConfig, IsNewerOrEqualConfig, NewerConfig, NewerOrEqualConfig, CV, TypeOK

LEMMA BecomeLeaderActiveConfigSetIdentical ==
ASSUME IndAuto, Next,
       NEW p \in Server,
       \E Q \in Quorums(config[p]) : BecomeLeader(p, Q)
PROVE \A s \in ActiveConfigSet' : s \in ActiveConfigSet
PROOF
    <4>ok. TypeOK BY DEF IndAuto
    <4>2. TAKE s \in ActiveConfigSet'
    <4>. CASE s # p
        <5>2. PICK Q \in Quorums(config[s])' : \A q \in Q : ~NewerConfig(CV(q), CV(s))' BY <4>2 DEF ActiveConfigSet, ConfigDisabled
        <5>3. Q \in Quorums(config[s])' /\ \A q \in Q : ~NewerConfig(CV(q), CV(s))' BY <5>2
        <5>4. s \in Server /\ Q \in SUBSET Server BY <4>ok, <4>2, <5>2, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
        <5>5. \A q \in Q : NewerOrEqualConfig(CV(s), CV(q))' BY <4>ok, <5>3, <5>4, NewerIsNotSymmetricAndNext
        <5>6. \A q \in Q : NewerOrEqualConfig(CV(q)', CV(q)) BY <5>4, ConfigsIncreaseMonotonically
        <5>7. \A q \in Q : NewerOrEqualConfig(CV(s)', CV(q)) BY <4>ok, <5>4, <5>5, <5>6, NewerOrEqualConfigTransitivityAndNext
        <5>8. CV(s) = CV(s)' BY DEF BecomeLeader, CV, TypeOK
        <5>9. \A q \in Q : NewerOrEqualConfig(CV(s), CV(q)) BY <5>7, <5>8
        <5>10. \A q \in Q : ~NewerConfig(CV(q), CV(s)) BY <4>ok, <5>4, <5>9, NewerIsNotSymmetric
        <5>11. Q \in Quorums(config[s]) BY <5>2, <5>3, <5>4 DEF BecomeLeader, Quorums, TypeOK
        <5>. QED BY <5>10, <5>11 DEF ActiveConfigSet, ConfigDisabled
    <4>. CASE s = p BY <4>ok, ElectedLeadersInActiveConfigSet
    <4>. QED OBVIOUS
    

LEMMA SendConfigActiveConfigSetIdenticalExceptRecipient ==
ASSUME IndAuto, Next,
       NEW u \in Server,
       NEW v \in Server,
       SendConfig(u, v)
PROVE \A n \in ActiveConfigSet' : n # v => n \in ActiveConfigSet
PROOF
    <4>ok. TypeOK BY DEF IndAuto
    <4>1. TAKE n \in ActiveConfigSet'
    <4>2. SUFFICES ASSUME n # v
          PROVE n \in ActiveConfigSet BY <4>1
    <4>3. PICK Q \in Quorums(config[n])' : \A q \in Q : ~NewerConfig(CV(q), CV(n))' BY <4>1 DEF ActiveConfigSet, ConfigDisabled
    <4>4. n \in Server /\ Q \in SUBSET Server BY <4>ok, <4>1, <4>3, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
    <4>5. \A q \in Q : NewerOrEqualConfig(CV(n), CV(q))' BY <4>ok, <4>3, <4>4, NewerIsNotSymmetricAndNext
    <4>6. \A q \in Q : NewerOrEqualConfig(CV(q)', CV(q)) BY <4>ok, <4>4, SendConfigImpliesNewerOrEqualConfig
    <4>7. \A q \in Q : NewerOrEqualConfig(CV(n)', CV(q)) BY <4>ok, <4>4, <4>5, <4>6, NewerOrEqualConfigTransitivityAndNext
    <4>8. CV(n) = CV(n)' BY <4>2 DEF SendConfig, CV, TypeOK
    <4>9. \A q \in Q : NewerOrEqualConfig(CV(n), CV(q)) BY <4>7, <4>8
    <4>10. \A q \in Q : ~NewerConfig(CV(q), CV(n)) BY <4>ok, <4>4, <4>9, NewerIsNotSymmetric
    <4>11. Q \in Quorums(config[n]) BY <4>2, <4>3, <4>4 DEF SendConfig, Quorums, TypeOK
    <4>. QED BY <4>10, <4>11 DEF ActiveConfigSet, ConfigDisabled

LEMMA QuorumsIdentical ==
ASSUME TypeOK
PROVE
    \A s \in Server : 
        /\ Quorums(config[s]) = Quorums(config[s])
        /\ Quorums(config[s]) = Quorums(config[s])
    BY ServerIsFinite DEF TypeOK,Quorums,Quorums,Quorums,Cardinality,Cardinality,Cardinality

LEMMA ReconfigImpliesInActiveConfigSet ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(s, newConfig)
PROVE s \in ActiveConfigSet
PROOF BY QuorumsIdentical DEF Reconfig, ConfigIsCommitted,
            ActiveConfigSet, ConfigDisabled, NewerConfig, CV, Quorums, TypeOK, QuorumsAt

LEMMA ReconfigImpliesCurrentTermGreaterThanConfigTerms ==
ASSUME IndAuto,
       NEW s \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(s, newConfig)
PROVE \A t \in Server : currentTerm[s] >= configTerm[t]
PROOF
    <1>1. s \in ActiveConfigSet BY ReconfigImpliesInActiveConfigSet DEF IndAuto
    <1>2. TAKE t \in Server
    <1>3. PICK Q \in Quorums(config[s]) : \A n \in Q : currentTerm[n] = currentTerm[s]
        BY QuorumsIdentical DEF Reconfig, ConfigIsCommitted, QuorumsAt
    <1>4. PICK n \in Q : currentTerm[n] >= configTerm[t] BY <1>1, <1>3 
    DEF IndAuto,Inv1758_1_0_def, Inv2973_1_1_def, ActiveConfigSet,Inv2973_1_1_def, Inv3246_1_2_def
    <1>5. currentTerm[s] = currentTerm[n] BY <1>3
    <1>. QED BY <1>4, <1>5 DEF Quorums

LEMMA ReconfigImpliesSameActiveConfigSet ==
ASSUME IndAuto,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(p, newConfig)
PROVE \A n \in ActiveConfigSet' : n \in ActiveConfigSet
    <4>ok. TypeOK BY DEF IndAuto
    <4>1. TAKE n \in ActiveConfigSet'
    <4>n. n \in Server BY <4>1 DEF ActiveConfigSet, ConfigDisabled, Quorums
    <4>2. PICK Q \in Quorums(config[n])' : \A q \in Q : ~NewerConfig(CV(q), CV(n))' BY <4>1 DEF ActiveConfigSet, ConfigDisabled
    <4>. CASE n = p
        <5>1. \E nQ \in Quorums(config[n]) : \A q \in nQ : CV(n) = CV(q)
            BY <4>ok, QuorumsIdentical DEF Reconfig, ConfigIsCommitted, Quorums, CV, QuorumsAt
        <5>. QED BY <4>ok, <5>1 DEF ActiveConfigSet, ConfigDisabled, NewerOrEqualConfig, NewerConfig, CV, Reconfig, TypeOK
    <4>. CASE n # p
        <5>1. Q \in Quorums(config[n])
            <6>1. config[n] = config'[n] BY DEF Reconfig, TypeOK
            <6>. QED BY <4>2, <6>1 DEF Quorums
        <5>2. \A q \in Q : ~NewerConfig(CV(q), CV(n))
            <6>1. p \notin Q
                <7>1. SUFFICES ASSUME p \in Q
                      PROVE FALSE OBVIOUS
                <7>2. currentTerm[p] >= configTerm[n] BY <4>n, ReconfigImpliesCurrentTermGreaterThanConfigTerms
                <7>3. configTerm[p] >= configTerm[n] BY <7>2 DEF Reconfig, IndAuto, Inv2973_1_1_def, Inv866_1_0_def
                <7>. CASE configTerm[p] > configTerm[n]
                    <8>1. configTerm'[p] > configTerm'[n]
                        BY <4>n, <7>2 DEF Reconfig, TypeOK, IndAuto, Inv1758_1_0_def, Inv866_1_0_def
                    <8>2. NewerConfig(CV(p), CV(n))' BY <4>n, <8>1 DEF Reconfig, NewerConfig, CV, TypeOK
                    <8>. QED BY <4>2, <7>1, <8>2
                <7>. CASE configTerm[p] = configTerm[n]
                    <8>1. configVersion[p] >= configVersion[n] BY <4>n, <4>ok 
                    DEF TypeOK, Reconfig, IndAuto, Inv1758_1_0_def, Inv2973_1_1_def,Inv866_1_0_def,Inv3915_1_1_def,
                    IsNewerConfig
                    <8>2. configVersion'[p] > configVersion'[n] BY <4>ok, <4>n, <8>1 DEF Reconfig, TypeOK
                    <8>3. NewerConfig(CV(p), CV(n))'
                        BY <4>n, <8>2 DEF Reconfig, NewerConfig, CV, IndAuto,  TypeOK, Inv1758_1_0_def,Inv866_1_0_def
                    <8>. QED BY <4>2, <7>1, <8>3
                <7>. QED BY <4>ok, <4>n, <7>3 DEF TypeOK
            <6>2. \A q \in Q : CV(q) = CV(q)' BY <4>2, <6>1 DEF Reconfig, CV, TypeOK
            <6>. QED BY <4>2, <6>2 DEF Reconfig, NewerConfig, CV
        <5>. QED BY <5>1, <5>2 DEF ActiveConfigSet, ConfigDisabled
    <4>. QED OBVIOUS
   
LEMMA NewerOrEqualConfigWithSameTermImpliesGreaterOrEqualVersion ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       NewerOrEqualConfig(CV(s), CV(t)),
       configTerm[s] = configTerm[t]
PROVE configVersion[s] >= configVersion[t]
PROOF
    <1>1. CASE CV(s) = CV(t) BY <1>1 DEF NewerOrEqualConfig, CV, TypeOK
    <1>2. CASE CV(s) # CV(t) BY <1>2 DEF NewerOrEqualConfig, NewerConfig, CV, TypeOK
    <1>. QED BY <1>1, <1>2

LEMMA NewerOrEqualImpliesConfigTermGreaterThanOrEqual ==
ASSUME TypeOK,
       NEW s \in Server,
       NEW t \in Server,
       NewerOrEqualConfig(CV(s), CV(t))
PROVE configTerm[s] >= configTerm[t]
PROOF BY DEF NewerOrEqualConfig, NewerConfig, CV, TypeOK   

COROLLARY ReconfigImpliesActiveConfigSetHaveSmallerOrEqualConfigTerm ==
ASSUME IndAuto,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(p, newConfig)
PROVE \A n \in Server : configTerm[p] >= configTerm[n]
BY ReconfigImpliesCurrentTermGreaterThanConfigTerms 
DEF Reconfig, IndAuto, Inv6243_1_1_def ,Inv2973_1_1_def,Inv1758_1_0_def,Inv866_1_0_def

LEMMA ReconfigImpliesActiveConfigSetHaveSameConfig ==
ASSUME IndAuto,
       NEW p \in Server,
       NEW newConfig \in SUBSET Server,
       Reconfig(p, newConfig)
PROVE \A s \in ActiveConfigSet' : config[s] = config[p]
PROOF
    <4>ok. TypeOK BY DEF IndAuto
    <4>. TAKE s \in ActiveConfigSet'
    <4>. s \in ActiveConfigSet BY ReconfigImpliesSameActiveConfigSet
    <4>. s \in Server BY DEF ActiveConfigSet, ConfigDisabled
    <4>1. PICK Q \in Quorums(config[s]) : \A n \in Q : ~NewerConfig(CV(n), CV(s)) BY DEF ActiveConfigSet, ConfigDisabled
    <4>2. PICK pQ \in Quorums(config[p]) : \A q \in pQ : CV(q) = CV(p)
        BY <4>ok, QuorumsIdentical DEF Reconfig, ConfigIsCommitted, CV, TypeOK, QuorumsAt
    <4>3. PICK q \in pQ : ~NewerConfig(CV(q), CV(s))
        BY <4>1, <4>2, ReconfigImpliesInActiveConfigSet DEF IndAuto,  Inv2973_1_1_def, QuorumsOverlap, ActiveConfigSet
    <4>4. NewerOrEqualConfig(CV(s), CV(q))
        BY <4>ok, <4>2, <4>3, NewerIsNotSymmetric, QuorumsAreNonEmpty DEF Quorums, TypeOK
    <4>5. configTerm[p] = configTerm[s]
        <5>1. configTerm[p] >= configTerm[s] BY ReconfigImpliesActiveConfigSetHaveSmallerOrEqualConfigTerm
        <5>2. configTerm[s] >= configTerm[q]
            BY <4>ok, <4>4, NewerOrEqualImpliesConfigTermGreaterThanOrEqual DEF Quorums, TypeOK
        <5>. QED BY <4>ok, <4>2, <5>1, <5>2 DEF CV, TypeOK
    <4>6. configVersion[p] = configVersion[s]
        <5>1. configVersion[p] >= configVersion[s]
            BY <4>5, <4>ok DEF Reconfig, IndAuto,  
            TypeOK, IsNewerConfig, Inv2973_1_1_def,Inv3915_1_1_def,Inv866_1_0_def
        <5>2. configVersion[s] >= configVersion[q]
            BY <4>ok, <4>2, <4>3, <4>4, <4>5, NewerOrEqualConfigWithSameTermImpliesGreaterOrEqualVersion DEF Quorums, CV, TypeOK
        <5>. QED BY <4>ok, <4>2, <5>1, <5>2 DEF CV, TypeOK
    <4>. QED BY <4>ok, <4>5, <4>6 DEF IndAuto, Inv2973_1_1_def,
    Inv1758_1_0_def,TypeOK,IsNewerConfig


------------------------------------------------------------------------


\* 
\* Proof for August 11, 2022 generated invariant.
\* 


THEOREM Init => IndAuto
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1> USE InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig
  <1>0. TypeOK
    BY InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def
  <1>1. Safety
    BY InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def
  <1>3. Inv2973_1_1_def
    BY InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent,
       StaticQuorumsOverlap,ConfigQuorumsOverlap 
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def
  <1>4. Inv1758_1_0_def
    BY InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def
  <1>5. Inv3915_1_1_def
    BY InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def
  <1>6. Inv3246_1_2_def
    BY InitTermType, ServerIsNonempty, ServerIsFinite, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
        Quorums
  <1>7. Inv866_1_0_def
    BY InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
    DEF OnePrimaryPerTerm, ConfigDisabled, NewerConfig, CV, IsNewerConfig,TypeOK,Init,Next,IndAuto,Safety,
        Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def
  <1>8. QED
    BY <1>0, <1>1, <1>3, <1>4, <1>5, <1>6, <1>7 DEF IndAuto
  
  
LEMMA ConfigsEqualIfNeitherNewer == 
ASSUME TypeOK
PROVE (\A i,j \in Server : 
            (~IsNewerConfig(j, i) /\ ~IsNewerConfig(i, j)) <=>
            (<<configVersion[i],configTerm[i]>> = <<configVersion[j],configTerm[j]>>))
BY DEF TypeOK,IsNewerConfig
            
            
LEMMA Equiv == 
Inv1758_1_0_def <=> ( \A i,j \in Server : (config[i] = config[j]) \/ ~(~IsNewerConfig(j, i) /\ ~(IsNewerConfig(i, j)))  )
BY DEF TypeOK,IsNewerConfig,Inv1758_1_0_def


Inv1758_1_0_def_restated == ( \A i,j \in Server : (<<configVersion[i],configTerm[i]>> = <<configVersion[j],configTerm[j]>>) =>  (config[i] = config[j]) )

Equiv3Expr ==
TypeOK =>
(Inv1758_1_0_def <=>
 Inv1758_1_0_def_restated)

LEMMA Equiv3 == 
    /\ Equiv3Expr 
    /\ Equiv3Expr'
BY DEF TypeOK,Equiv3Expr,IsNewerConfig,Inv1758_1_0_def, Inv1758_1_0_def_restated
  
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1> USE InitTermType, ServerIsNonempty, QuorumsExistForNonEmptySets, QuorumsAreNonEmpty, PrimaryAndSecondaryAreDifferent
  <1> USE DEF ReconfigAction,SendConfigAction,BecomeLeaderAction,UpdateTermsAction,IndAuto,UpdateTermsExpr,OnePrimaryPerTerm
  <1>0. TypeOK'
    <2>1. CASE ReconfigAction
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig
    <2>2. CASE SendConfigAction
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>3. CASE BecomeLeaderAction
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms,UpdateTermsExpr
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
    
  <1>1. Safety'
    <2>ok. TypeOK BY DEF IndAuto
    <2>1. CASE ReconfigAction
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig
    <2>2. CASE SendConfigAction
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      SendConfig
    <2>3. CASE BecomeLeaderAction
        <3>1. SUFFICES ASSUME TRUE
              PROVE \A s \in Server : state'[s] = Primary =>
                         \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
              BY DEF Safety,OnePrimaryPerTerm
        <3>2. TAKE s \in Server
        <3>3. SUFFICES ASSUME state'[s] = Primary
              PROVE \A t \in Server : (state'[t] = Primary /\ currentTerm'[s] = currentTerm'[t]) => s = t
              BY <3>1
        <3>4. TAKE t \in Server
        <3>5. SUFFICES ASSUME state'[t] = Primary, currentTerm'[s] = currentTerm'[t], s # t
              PROVE FALSE BY <3>3
        <3>6. \/ \E Q \in Quorums(config[s]) : BecomeLeader(s, Q) /\ BecomeLeader(s, Q)
              \/ \E Q \in Quorums(config[t]) : BecomeLeader(t, Q) /\ BecomeLeader(t, Q)
            <4>a. SUFFICES ASSUME /\ ~\E Q \in Quorums(config[s]) : BecomeLeader(s, Q) /\ BecomeLeader(s, Q)
                                  /\ ~\E Q \in Quorums(config[t]) : BecomeLeader(t, Q) /\ BecomeLeader(t, Q)
                  PROVE FALSE OBVIOUS
            <4>p. PICK p \in Server : \E Q \in Quorums(config[p]) : BecomeLeader(p, Q) /\ BecomeLeader(p, Q) BY <2>3
            <4>q. PICK Q \in Quorums(config[p]) : BecomeLeader(p, Q) /\ BecomeLeader(p, Q) BY <4>p
            <4>1. currentTerm[s] # currentTerm'[s] \/ currentTerm[t] # currentTerm'[t]
                BY <2>3, <3>2, <3>3, <3>4, <3>5 DEF BecomeLeader, IndAuto, Safety,OnePrimaryPerTerm, TypeOK
            <4>2. s \in Q \/ t \in Q BY <4>q, <4>1 DEF BecomeLeader, TypeOK
            <4>3. s # p /\ t # p BY <4>a, <4>p DEF TypeOK
            <4>4. state'[s] = Secondary \/ state'[t] = Secondary BY <4>p, <4>q, <4>2, <4>3 DEF BecomeLeader, TypeOK
            <4>. QED BY <4>4, <3>3, <3>5, PrimaryAndSecondaryAreDifferent
        \* if s becomes leader then it's in the ActiveConfigSet, and thus \E n \in Q : currentTerm[n] > currentTerm[s], a contradiction
        <3>. CASE \E Q \in Quorums(config[s]) : BecomeLeader(s, Q)
            <4>1. PICK Q \in Quorums(config[s]) : BecomeLeader(s, Q) OBVIOUS
            <4>2. currentTerm[t] > currentTerm[s]
                <5>1. t \notin Q BY <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF BecomeLeader
                <5>2. currentTerm[t] = currentTerm'[t] BY <4>1, <5>1 DEF BecomeLeader, TypeOK
                <5>. QED BY <2>ok, <5>2, <3>5 DEF BecomeLeader, TypeOK
            <4>3. currentTerm[t] = configTerm[t]
                <5>1. t \notin Q BY <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF BecomeLeader
                <5>2. state[t] = Primary BY <2>ok, <5>1, <3>5 DEF BecomeLeader, TypeOK
                <5>. QED BY <5>2 DEF IndAuto, Inv866_1_0_def
            <4>4. s \in ActiveConfigSet BY <3>2, <4>1, ElectedLeadersInActiveConfigSet DEF IndAuto
            <4>5. \E n \in Q : currentTerm[n] >= configTerm[t] BY <3>2, <4>1, <4>4 DEF IndAuto,ActiveConfigSet,Inv3246_1_2_def
            <4>6. \E n \in Q : currentTerm[n] > currentTerm[s] BY <2>ok, <3>2, <4>1, <4>2, <4>3, <4>5 DEF Quorums, TypeOK
            <4>. QED BY <2>ok, <3>2, <4>1, <4>6 DEF BecomeLeader, CanVoteForConfig, Quorums, TypeOK
        <3>. CASE \E Q \in Quorums(config[t]) : BecomeLeader(t, Q)
            <4>1. PICK Q \in Quorums(config[t]) : BecomeLeader(t, Q) OBVIOUS
            <4>2. currentTerm[s] > currentTerm[t]
                <5>1. s \notin Q BY <3>3, <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF BecomeLeader
                <5>2. currentTerm[s] = currentTerm'[s] BY <4>1, <5>1 DEF BecomeLeader, TypeOK
                <5>. QED BY <2>ok, <5>2, <3>5 DEF BecomeLeader, TypeOK
            <4>3. currentTerm[s] = configTerm[s]
                <5>1. s \notin Q BY <3>3, <3>5, <4>1, PrimaryAndSecondaryAreDifferent DEF BecomeLeader
                <5>2. state[s] = Primary BY <2>ok, <5>1, <3>3, <3>5 DEF BecomeLeader, TypeOK
                <5>. QED BY <5>2 DEF IndAuto, Inv866_1_0_def
            <4>4. t \in ActiveConfigSet BY <3>2, <4>1, ElectedLeadersInActiveConfigSet DEF IndAuto
            <4>5. \E n \in Q : currentTerm[n] >= configTerm[s] BY <3>2, <4>1, <4>4 DEF IndAuto, Inv852_1_2_def, ActiveConfigSet,Inv3246_1_2_def
            <4>6. \E n \in Q : currentTerm[n] > currentTerm[t] BY <2>ok, <3>2, <4>1, <4>2, <4>3, <4>5 DEF Quorums, TypeOK
            <4>. QED BY <2>ok, <3>2, <4>1, <4>6 DEF BecomeLeader, CanVoteForConfig, Quorums, TypeOK
        <3>. QED BY <3>6
      
      
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
  <1>3. Inv2973_1_1_def'
    <2>ok. TypeOK BY DEF IndAuto
    <2>1. CASE ReconfigAction
        <3>p. PICK p \in Server, newConfig \in SUBSET Server : Reconfig(p, newConfig) BY <2>1
        <3>1. p \in ActiveConfigSet BY <3>p, ReconfigImpliesInActiveConfigSet DEF IndAuto
        <3>2. \A s \in ActiveConfigSet' : config[s] = config[p] BY <3>p, ReconfigImpliesActiveConfigSetHaveSameConfig DEF IndAuto,ActiveConfigSet
        <3>3. \A t \in ActiveConfigSet' : config'[t] = newConfig \/ config'[t] = config[p]
            BY <3>p, <3>2 DEF Reconfig, TypeOK
        <3>4. QuorumsOverlap(config[p], newConfig) BY <2>ok, <3>p DEF Reconfig, TypeOK
        <3>. QED BY <2>ok, <3>p, <3>3, <3>4, QuorumsOverlapIsCommutative, StaticQuorumsOverlap 
                 DEF Inv2973_1_1_def, QuorumsOverlap, Quorums, TypeOK, ActiveConfigSet
    <2>2. CASE SendConfigAction
        <3>1. PICK u \in Server, v \in Server : SendConfig(u, v) BY <2>2
        <3>2. \A n \in Server : n # v => config[n] = config'[n] BY <3>1 DEF SendConfig, TypeOK
        <3>3. \A n \in ActiveConfigSet' : n # v => n \in ActiveConfigSet BY <3>1, SendConfigActiveConfigSetIdenticalExceptRecipient DEF IndAuto
        <3>4. \A s,t \in ActiveConfigSet' : (s # v /\ t # v) => QuorumsOverlap(config[s], config[t])'
            <4>1. \A s,t \in ActiveConfigSet' : (s # v /\ t # v) => QuorumsOverlap(config[s], config[t]) 
            BY <3>3 DEF IndAuto, Inv2973_1_1_def, ActiveConfigSet
            <4>. QED BY <3>2, <4>1 DEF ActiveConfigSet, ConfigDisabled
        <3>5. \A s,t \in ActiveConfigSet' : (s = v /\ t # v) => QuorumsOverlap(config[s], config[t])'
            <4>1. TAKE s,t \in ActiveConfigSet'
            <4>2. SUFFICES ASSUME s = v, t # v
                  PROVE QuorumsOverlap(config[s], config[t])' OBVIOUS
            <4>. CASE u \in ActiveConfigSet'
                <5>1. t \in ActiveConfigSet /\ u \in ActiveConfigSet BY <3>1, <3>3, <4>1, <4>2 DEF SendConfig, IsNewerConfig, TypeOK
                <5>2. QuorumsOverlap(config[u], config[t]) 
                  BY <5>1, QuorumsOverlapIsCommutative 
                  DEF IndAuto, Inv2973_1_1_def, ActiveConfigSet
                <5>3. config'[t] = config[t] BY <3>1, <4>2 DEF SendConfig, TypeOK
                <5>4. config'[s] = config[u] BY <2>ok, <3>1, <4>2, TypeOKAndNext DEF SendConfig, TypeOK
                <5>. QED BY <5>2, <5>3, <5>4
            <4>. CASE u \notin ActiveConfigSet'
                BY <2>ok, <3>1, <4>1, <4>2 DEF SendConfig, ActiveConfigSet, ConfigDisabled, NewerConfig, CV, TypeOK
            <4>. QED OBVIOUS
        <3>6. \A s,t \in ActiveConfigSet' : (s # v /\ t = v) => QuorumsOverlap(config[s], config[t])'
            BY <2>ok, <3>5, QuorumsOverlapIsCommutative, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, TypeOK
        <3>7. \A s,t \in ActiveConfigSet' : (s = v /\ t = v) => QuorumsOverlap(config[s], config[t])'
            BY <2>ok, StaticQuorumsOverlap, TypeOKAndNext DEF ActiveConfigSet, ConfigDisabled, QuorumsOverlap, TypeOK
        <3>. QED BY <3>4, <3>5, <3>6, <3>7 DEF Inv716_1_1_def, Inv2973_1_1_def, ActiveConfigSet
    <2>3. CASE BecomeLeaderAction
        <3>1. \A s \in Server : Quorums(config'[s]) = Quorums(config[s]) BY <2>3 DEF BecomeLeader, Quorums
        <3>2. \A s,t \in Server : QuorumsOverlap(config[s],config[t]) <=> QuorumsOverlap(config[s],config[t])' BY <3>1 DEF QuorumsOverlap
        <3>3. \A s \in ActiveConfigSet' : s \in ActiveConfigSet 
          BY <2>3, BecomeLeaderActiveConfigSetIdentical 
          DEF ActiveConfigSet
        <3>. QED BY <3>2, <3>3 DEF IndAuto, Inv2973_1_1_def, ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,
      Inv2973_1_1_def,
      UpdateTerms,NewerConfig,CV,
      QuorumsOverlap, Quorums, ConfigDisabled, NewerConfig, CV  
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
    
  <1>4. Inv1758_1_0_def'
    <2>ok. TypeOK BY DEF IndAuto
    <2>1. CASE ReconfigAction
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,IsNewerConfig
    <2>2. CASE SendConfigAction
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      SendConfig,IsNewerConfig
    <2>3. CASE BecomeLeaderAction
        <3> USE Equiv3 DEF Equiv3Expr
        <3>0. TypeOK' BY <2>3 DEF TypeOK, BecomeLeader
        <3>1. Inv1758_1_0_def_restated'
            <4>. SUFFICES ASSUME TRUE
                PROVE \A s,t \in Server :
                        (<<configVersion'[s],configTerm'[s]>> = <<configVersion'[t],configTerm'[t]>>) => config'[s] = config'[t]
                BY DEF Inv1758_1_0_def,Inv1758_1_0_def_restated,IsNewerConfig,IndAuto, TypeOK
            <4>. TAKE s,t \in Server
            <4>. PICK p \in Server : \E Q \in Quorums(config[p]) : BecomeLeader(p, Q) BY <2>3
            <4>. CASE s = p \/ t = p 
              BY <2>ok,ConfigVersionAndTermUniqueAndNext_BecomeLeader
              DEF IndAuto,TypeOK,Inv1758_1_0_def_restated
            <4>. CASE s # p /\ t # p BY DEF BecomeLeader, TypeOK, IndAuto, Inv1758_1_0_def,Inv1758_1_0_def,IsNewerConfig
            <4>. QED OBVIOUS
       
        <3>2. QED BY <2>ok,<3>0,<3>1,Equiv3 DEF Equiv3Expr
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms,IsNewerConfig
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
    
  <1>5. Inv3915_1_1_def'
    <2>1. CASE ReconfigAction
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,IsNewerConfig
    <2>2. CASE SendConfigAction
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      SendConfig,IsNewerConfig
    <2>3. CASE BecomeLeaderAction
        <3>1. PICK s \in Server : \E Q \in Quorums(config[s]) : BecomeLeader(s, Q) BY <2>3
        <3>2. \A t \in Server : currentTerm[s] >= configTerm[t] BY <3>1, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF IndAuto
        <3>. QED 
          BY <3>1, <3>2 
          DEF BecomeLeader, TypeOK, IndAuto, Inv1925_1_1_def,Inv3915_1_1_def,IsNewerConfig
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      UpdateTerms,IsNewerConfig
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
    
  <1>6. Inv3246_1_2_def'
    <2>ok. TypeOK BY DEF IndAuto
    <2>1. CASE ReconfigAction
        <3>p. PICK p \in Server, newConfig \in SUBSET Server : Reconfig(p, newConfig) BY <2>1
        <3>1. SUFFICES ASSUME TRUE
              PROVE \A s \in Server : \A t \in ActiveConfigSet' :
                \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
              BY DEF Inv3246_1_2_def, ActiveConfigSet, ConfigDisabled
        <3>2. TAKE s \in Server
        <3>3. TAKE t \in ActiveConfigSet'
        <3>4. config[t] = config[p] BY <3>p, <3>3, ReconfigImpliesActiveConfigSetHaveSameConfig DEF IndAuto
        <3>5. CASE t # p
            <4>1. config'[t] = config[t] /\ config'[t] = config[p] BY <3>p, <3>4, <3>5 DEF Reconfig, TypeOK
            <4>2. PICK pQ \in Quorums(config[p]) : \A n \in pQ : currentTerm[n] = currentTerm[p]
                BY <3>p, QuorumsIdentical DEF Reconfig, QuorumsAt, ConfigIsCommitted, IndAuto
            <4>3. TAKE tQ \in Quorums(config'[t])
            <4>4. tQ \in Quorums(config[t]) BY <4>1, <4>3
            <4>5. QuorumsOverlap(config[t], config[p])
                BY <3>3, ReconfigImpliesSameActiveConfigSet, <3>p, ReconfigImpliesInActiveConfigSet 
                DEF IndAuto, Inv716_1_1_def, Inv2973_1_1_def, ActiveConfigSet
            <4>6. PICK n \in tQ : n \in pQ BY <4>2, <4>4, <4>5 DEF QuorumsOverlap
            <4>7. currentTerm[n] >= configTerm[s] BY <3>p, <3>2, <4>2, <4>6, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF IndAuto
            <4>8. currentTerm'[n] >= configTerm'[s]
                BY <3>p, <3>2, <3>3, <4>4, <4>6, <4>7, ReconfigImpliesConfigTermUnchanged DEF Reconfig, Quorums, TypeOK
            <4>. QED BY <3>1, <3>2, <3>3, <4>3, <4>8
        <3>6. CASE t = p
            <4>1. PICK pQ \in Quorums(config[p]) : \A n \in pQ : currentTerm[n] = currentTerm[p]
                BY <3>p DEF Reconfig, ConfigIsCommitted, IndAuto, QuorumsAt
            <4>2. config'[t] = newConfig BY <2>ok, <3>p, <3>6 DEF Reconfig, TypeOK
            <4>3. TAKE tQ \in Quorums(config'[t])
            <4>4. QuorumsOverlap(config[p], newConfig) BY <2>ok, <3>p, <4>1, <4>2, <4>3 DEF Reconfig, TypeOK
            <4>5. PICK n \in tQ : n \in pQ BY <4>1, <4>2, <4>3, <4>4 DEF QuorumsOverlap
            <4>6. currentTerm[n] >= configTerm[s] BY <3>p, <3>2, <4>1, <4>5, ReconfigImpliesCurrentTermGreaterThanConfigTerms DEF IndAuto
            <4>7. currentTerm'[n] >= configTerm'[s]
                BY <3>p, <3>2, <3>3, <4>3, <4>5, <4>6, ReconfigImpliesConfigTermUnchanged DEF Reconfig, Quorums, QuorumsAt, TypeOK
            <4>. QED BY <3>1, <3>2, <3>3, <4>3, <4>7
        <3>. QED BY <3>5, <3>6
    <2>2. CASE SendConfigAction
        <3>1. PICK u,v \in Server : SendConfig(u, v) BY <2>2
        <3>2. SUFFICES ASSUME TRUE
              PROVE 
                \A s \in Server : \A t \in ActiveConfigSet' :
                \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
              BY <2>ok DEF Inv3246_1_2_def, ActiveConfigSet, TypeOK, ConfigDisabled
        <3>3. TAKE s \in Server
        <3>4. TAKE t \in ActiveConfigSet'
        <3>5. CASE t # v
            <4>1. t \in ActiveConfigSet BY <3>1, <3>4, <3>5, SendConfigActiveConfigSetIdenticalExceptRecipient DEF IndAuto
            <4>2. CASE s # v
                <5>1. \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[s] 
                BY <4>1 DEF IndAuto, Inv3246_1_2_def, ActiveConfigSet
                <5>. QED BY <3>1, <3>5, <4>2, <5>1 DEF SendConfig, TypeOK
            <4>3. CASE s = v
                <5>1. \A Q \in Quorums(config[t]) : \E n \in Q : currentTerm[n] >= configTerm[u] 
                BY <3>1, <4>1 DEF IndAuto, Inv3246_1_2_def, ActiveConfigSet
                <5>2. configTerm'[s] = configTerm[u] BY <2>ok, <3>1, <4>3 DEF SendConfig, TypeOK
                <5>. QED BY <3>1, <3>5, <4>2, <5>1, <5>2 DEF SendConfig, TypeOK
            <4>. QED BY <4>2, <4>3
        <3>6. CASE t = v
            <4>u. u # v BY <3>1 DEF SendConfig, IsNewerConfig, TypeOK
            <4>1. u \in ActiveConfigSet' BY <2>ok, <3>1, <3>6 DEF SendConfig, ActiveConfigSet, ConfigDisabled, NewerConfig, CV, TypeOK
            <4>2. u \in ActiveConfigSet BY <3>1, <4>1, <4>u, SendConfigActiveConfigSetIdenticalExceptRecipient DEF IndAuto
            <4>3. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm[n] >= configTerm[s] 
            BY <3>1, <4>2 DEF IndAuto, Inv852_1_2_def, Inv3246_1_2_def, ActiveConfigSet
            <4>4. config'[t] = config[u] BY <2>ok, <3>1, <3>6 DEF SendConfig, TypeOK
            <4>5. CASE s # v
                <5>1. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
                    BY <3>1, <4>u, <4>3, <4>5 DEF SendConfig, TypeOK
                <5>. QED BY <4>4, <5>1
            <4>6. CASE s = v
                <5>1. \A Q \in Quorums(config[u]) : \E n \in Q : currentTerm[n] >= configTerm[u]
                    BY <3>1, <4>2 DEF IndAuto, Inv852_1_2_def, Inv3246_1_2_def, ActiveConfigSet
                <5>. QED BY <2>ok, <3>1, <4>4, <4>6, <5>1 DEF SendConfig, TypeOK
            <4>. QED BY <4>5, <4>6
        <3>. QED BY <3>5, <3>6
    <2>3. CASE BecomeLeaderAction
        <3>p. PICK p \in Server : \E Q \in Quorums(config[p]) : BecomeLeader(p, Q) BY <2>3
        <3>q. PICK pQ \in Quorums(config[p]) : BecomeLeader(p, pQ) BY <3>p
        <3>1. SUFFICES ASSUME TRUE
              PROVE \A s \in Server : \A t \in ActiveConfigSet' :
                \A Q \in Quorums(config'[t]) : \E n \in Q : currentTerm'[n] >= configTerm'[s]
              BY DEF Inv3246_1_2_def, ActiveConfigSet, ConfigDisabled
        <3>2. TAKE s \in Server
        <3>3. TAKE t \in ActiveConfigSet'
        <3>4. t \in ActiveConfigSet BY <2>3, <3>3, BecomeLeaderActiveConfigSetIdentical DEF TypeOK
        <3>5. TAKE Q \in Quorums(config'[t])
        <3>6. Q \in Quorums(config[t]) BY <2>3, <3>4, <3>5 DEF BecomeLeader, ActiveConfigSet, ConfigDisabled
        <3>7. PICK n \in Q : currentTerm[n] >= configTerm[s] 
            BY <3>2, <3>4, <3>6 DEF IndAuto, Inv3246_1_2_def, ActiveConfigSet
        <3>n. n \in Server BY <2>ok, <3>6, <3>7 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
        <3>8. CASE n \in pQ
            <4>1. currentTerm'[p] >= configTerm'[s]
                <5>1. currentTerm[p] >= configTerm[s] BY <3>p, ElectedLeadersCurrentTermGreaterThanConfigTerms DEF TypeOK
                <5>2. CASE s # p
                    <6>1. configTerm'[s] = configTerm[s] BY <3>p, <5>2 DEF BecomeLeader, TypeOK
                    <6>2. currentTerm'[p] >= currentTerm[p] BY <2>ok, <3>p DEF BecomeLeader, TypeOK
                    <6>. QED BY <2>ok, <5>1, <6>1, <6>2, TypeOKAndNext DEF TypeOK
                <5>3. CASE s = p BY <2>ok, <3>p, <5>3 DEF BecomeLeader, TypeOK
                <5>. QED BY <5>2, <5>3
            <4>2. currentTerm'[n] = currentTerm'[p] BY <2>ok, <3>p, <3>q, <3>8 DEF BecomeLeader, Quorums, TypeOK
            <4>. QED BY <3>7, <4>1, <4>2
        <3>9. CASE n \notin pQ
            <4>1. currentTerm'[n] = currentTerm[n] BY <3>p, <3>q, <3>n, <3>9 DEF BecomeLeader, TypeOK
            <4>2. CASE s # p BY <2>ok, <3>p, <3>7, <4>1, <4>2 DEF BecomeLeader, TypeOK
            <4>3. CASE s = p
                <5>1. s \in ActiveConfigSet BY <3>p, <4>3, ElectedLeadersInActiveConfigSet DEF IndAuto
                <5>2. QuorumsOverlap(config[t], config[s]) 
                  BY <3>4, <5>1 
                  DEF IndAuto, Inv716_1_1_def, Inv2973_1_1_def, ActiveConfigSet
                <5>3. PICK q \in pQ : q \in Q BY <3>6, <3>p, <3>q, <4>3, <5>2 DEF QuorumsOverlap
                <5>4. currentTerm'[q] >= currentTerm'[s] \* their currentTerm's are equal because the update on q's
                                                         \* currentTerm is atomic (as well as p's)
                    BY <2>ok, <3>p, <3>q, <4>3, <5>3, TypeOKAndNext DEF BecomeLeader, Quorums, TypeOK
                <5>5. currentTerm'[s] = configTerm'[s] BY <2>ok, <3>p, <4>3 DEF BecomeLeader, TypeOK
                <5>6. q \in Server BY <2>ok, <3>4, <3>6, <5>3 DEF ActiveConfigSet, ConfigDisabled, Quorums, TypeOK
                <5>. QED BY <5>3, <5>4, <5>5, <5>6, TypeOKAndNext DEF TypeOK
            <4>. QED BY <4>2, <4>3
        <3>. QED BY <3>8, <3>9
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      UpdateTerms,ConfigDisabled,NewerConfig,CV
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
    
  <1>7. Inv866_1_0_def'
    <2>1. CASE ReconfigAction
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>2. CASE SendConfigAction
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>3. CASE BecomeLeaderAction
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>4. CASE UpdateTermsAction
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,Safety,
      Inv2973_1_1_def,Inv1758_1_0_def,Inv3915_1_1_def,Inv3246_1_2_def,Inv866_1_0_def,
      Reconfig,SendConfig,BecomeLeader,UpdateTerms
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
    
  <1>8. QED
    BY <1>0,<1>1,<1>3, <1>4, <1>5, <1>6, <1>7 DEF IndAuto

====