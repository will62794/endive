---- MODULE majorityset_leader_election_IndProofs ----
EXTENDS majorityset_leader_election, FiniteSetTheorems, TLAPS

\* endive.py stats
\* -----------------
\* date: 2022-08-05T19:42:54.969041
\* is_inductive: True
\* inv_size: 4
\* invcheck_duration_secs: 6.761046886444092
\* ctielimcheck_duration_secs: 16.151755809783936
\* ctigen_duration_secs: 16.04582977294922
\* total_duration_secs: 39.190558195114136
\* total_num_ctis_eliminated: 10000
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 374
\* total_num_invs_checked: 5640
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
Inv172_1_0_def == \A VARI \in Node : \A VARJ \in Node : (VARI \in vote[VARJ]) \/ (~(VARJ \in voters[VARI]))
Inv396_1_1_def == \A VARI \in Node : (voters[VARI] \in Majority) \/ (~(VARI \in leader))
Inv1537_2_2_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARI = VARK /\ vote = vote) \/ (~(VARI \in vote[VARJ])) \/ (~(VARK \in vote[VARJ]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv172_1_0_def
  /\ Inv396_1_1_def
  /\ Inv1537_2_2_def


ASSUME MajorityIntersect == \A m1,m2 \in Majority : m1 \cap m2 # {}
ASSUME MajorityNonEmpty == Majority # {} /\ \A s \in Majority : s # {}
ASSUME NodeFinite == IsFiniteSet(Node) /\ Node # {}
ASSUME NatTimesTwoIneq == \A a,b \in Nat : (a >= b) => (a*2 >= b*2)
ASSUME NatIneqTrans == \A a,b,c \in Nat : (a >= b /\ b > c) => (a > c)


LEMMA MajorityCupIsAMajority ==
ASSUME IndAuto,
       NEW M \in Majority,
       NEW n \in Node
PROVE (M \cup {n}) \in Majority
    <1>1. IsFiniteSet(M) BY NodeFinite, FS_Subset DEF Majority
    <1>.  DEFINE MNcard == Cardinality(M \cup {n})
    <1>.  DEFINE Mcard == Cardinality(M)
    <1>2. MNcard \in Nat /\ Mcard \in Nat BY <1>1, FS_CardinalityType, FS_AddElement
    <1>3. MNcard = Mcard \/ MNcard = Mcard+1 BY <1>1, FS_AddElement
    <1>.  HIDE DEF MNcard, Mcard
    <1>4. MNcard >= Mcard BY <1>1, <1>2, <1>3
    <1>5. MNcard*2 >= Mcard*2 BY <1>2, <1>4, NatTimesTwoIneq
    <1>6. Mcard*2 > Cardinality(Node) BY DEF Mcard, Majority
    <1>7. MNcard*2 > Cardinality(Node)
        <2>1. Cardinality(Node) \in Nat BY NodeFinite, FS_CardinalityType, NatIneqTrans
        <2>2. (MNcard*2) \in Nat /\ (Mcard) \in Nat BY <1>2
        <2>. QED BY <2>1, <2>2, <1>5, <1>6, NatIneqTrans
    <1>. QED BY <1>7 DEF MNcard, Majority

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def
  <1>2. Safety
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def
  <1>3. Inv172_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def
  <1>4. Inv396_1_1_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def
  <1>5. Inv1537_2_2_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote

  <1>2. Safety'
    <2>1. CASE \E n1,n2 \in Node : Voting(n1,n2)
      BY <2>1, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote
    <2>2. CASE \E voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs)
      BY <2>2, MajorityIntersect,MajorityNonEmpty,NodeFinite,FS_Subset DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote

    <2>3. CASE \E n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs)
        <3>1. PICK n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs) BY <2>3
        <3>2. voters[n] \in Majority BY <3>1 DEF BecomeLeader
        <3>3. SUFFICES ASSUME NEW x \in Node,
                              NEW y \in Node,
                              x \in leader',
                              y \in leader',
                              x # y
              PROVE FALSE BY DEF Safety
        <3>4. n = x \/ n = y BY <3>1, <3>3 DEF IndAuto, Safety, BecomeLeader
        <3>5. CASE n = x
            <4>1. y \in leader BY <3>1, <3>3, <3>5 DEF BecomeLeader, IndAuto, TypeOK
            <4>2. voters[y] \in Majority BY <4>1 DEF IndAuto, Inv396_1_1_def
            <4>3. \E p \in Node : p \in voters[n] /\ p \in voters[y] BY <3>2, <4>2, MajorityIntersect DEF IndAuto, TypeOK
            <4>. QED BY <3>3, <3>5, <4>3 DEF IndAuto, Inv172_1_0_def, Inv1537_2_2_def
        <3>6. CASE n = y
            <4>1. x \in leader BY <3>1, <3>3, <3>6 DEF BecomeLeader, IndAuto, TypeOK
            <4>2. voters[x] \in Majority BY <4>1 DEF IndAuto, Inv396_1_1_def
            <4>3. \E p \in Node : p \in voters[n] /\ p \in voters[x] BY <3>2, <4>2, MajorityIntersect DEF IndAuto, TypeOK
            <4>. QED BY <3>3, <3>6, <4>3 DEF IndAuto, Inv172_1_0_def, Inv1537_2_2_def
        <3>. QED BY <3>4, <3>5, <3>6

    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next

  <1>3. Inv172_1_0_def'
    <2>1. CASE \E n1,n2 \in Node : Voting(n1,n2)
      BY <2>1, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Inv172_1_0_def,Voting,DidNotVote

    <2>2. CASE \E voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs)
        <3>1. PICK voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs) BY <2>2
        <3>2. SUFFICES \A VARI,VARJ,VARK \in Node : ~(VARI \in voters'[VARJ]) \/ (VARJ \in vote'[VARI]) BY DEF Inv172_1_0_def
        <3>.  TAKE i,j,k \in Node
        <3>3. ~(i \in voters[j]) \/ (j \in vote[i]) BY DEF IndAuto, Inv172_1_0_def
        <3>4. CASE ~(i \in voters[j]) BY <3>1, <3>4 DEF ReceiveVote, IndAuto, TypeOK, Inv172_1_0_def
        <3>5. CASE (j \in vote[i]) BY <3>1, <3>4 DEF ReceiveVote, IndAuto, TypeOK, Inv172_1_0_def
        <3>. QED BY <3>3, <3>4, <3>5

    <2>3. CASE \E n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs)
      BY <2>3, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next

  <1>4. Inv396_1_1_def'
    <2>1. CASE \E n1,n2 \in Node : Voting(n1,n2)
      BY <2>1, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote

    <2>2. CASE \E voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs)
        <3>1. PICK voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs) BY <2>2
        <3>2. SUFFICES \A VARI,VARJ,VARK \in Node : (voters'[VARI] \in Majority) \/ ~(VARI \in leader') BY DEF Inv396_1_1_def
        <3>.  TAKE i,j,k \in Node
        <3>3. (voters[i] \in Majority) \/ ~(i \in leader) BY DEF IndAuto, Inv396_1_1_def
        <3>4. CASE (voters[i] \in Majority)
            <4>1. CASE n = i BY <3>1, <3>4, <4>1, MajorityCupIsAMajority DEF ReceiveVote, IndAuto, TypeOK, Inv396_1_1_def
            <4>2. CASE n # i BY <3>1, <3>4, <4>2 DEF ReceiveVote, IndAuto, TypeOK, Inv396_1_1_def
            <4>. QED BY <4>1, <4>2
        <3>5. CASE ~(i \in leader) BY <3>1, <3>4 DEF ReceiveVote, IndAuto, TypeOK, Inv396_1_1_def
        <3>. QED BY <3>3, <3>4, <3>5

    <2>3. CASE \E n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs)
      BY <2>3, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next

  <1>5. Inv1537_2_2_def'
    <2>1. CASE \E n1,n2 \in Node : Voting(n1,n2)
      BY <2>1, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Inv1537_2_2_def,Voting,DidNotVote
    <2>2. CASE \E voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs)
      BY <2>2, MajorityIntersect,MajorityNonEmpty,NodeFinite DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote
    <2>3. CASE \E n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs)
      BY <2>3, MajorityIntersect,MajorityNonEmpty DEF TypeOK,IndAuto,Safety,Inv172_1_0_def,Inv396_1_1_def,Inv1537_2_2_def,Voting,ReceiveVote,BecomeLeader,DidNotVote
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next

  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto

====
