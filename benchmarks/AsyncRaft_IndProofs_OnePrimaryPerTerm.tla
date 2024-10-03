--------------------------------- MODULE AsyncRaft_IndProofs_OnePrimaryPerTerm ---------------------------------
EXTENDS AsyncRaft,TLAPS, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, FiniteSets

THEOREM FS_Doubleton ==
  /\ \A x,y : IsFiniteSet({x,y}) /\ Cardinality({x,y}) = 2
  /\ \A S : IsFiniteSet(S) => (Cardinality(S) = 2 <=> \E x,y: S = {x,y} /\ x # y)

LEMMA QuorumsExistForNonEmptySets ==
ASSUME NEW S, IsFiniteSet(S), S # {}
PROVE Quorum # {}
PROOF BY FS_EmptySet, FS_CardinalityType DEF Quorum

LEMMA QuorumsAreServerSubsets ==
ASSUME TypeOK, NEW s \in Server
PROVE Quorum \subseteq SUBSET Server
PROOF BY DEF Quorum, TypeOK

LEMMA AddingToQuorumRemainsQuorum == \A Q \in Quorum : \A s \in Server : Q \in Quorum => Q \cup {s} \in Quorum

\* If the intersection of two server sets is empty, then they can't both be quorums.
LEMMA EmptyIntersectionImpliesNotBothQuorums == 
    \A s1 \in SUBSET Server :
    \A s2 \in SUBSET Server :
        (s1 \cap s2 = {}) => ~(s1 \in Quorum /\ s2 \in Quorum)


LEMMA StaticQuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}





-----------------------------------------------------------------------------------------------------------


\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 9
\* num proof obligations: 81
Safety == H_OnePrimaryPerTerm
Inv28_8e53_R0_0_I1 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv1270_3acc_R0_0_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv20_42ac_R1_0_I0 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv10_2c32_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv11_e30e_R3_0_I1 == \A VARI \in Server : ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower)))
Inv3_82b3_R3_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv6_f533_R3_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv5_3715_R5_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv28_8e53_R0_0_I1
  /\ Inv20_42ac_R1_0_I0
  /\ Inv11_e30e_R3_0_I1
  /\ Inv5_3715_R5_0_I0
  /\ Inv6_f533_R3_2_I0
  /\ Inv10_2c32_R1_1_I1
  /\ Inv3_82b3_R3_1_I0
  /\ Inv1270_3acc_R0_0_I1


\* mean in-degree: 1.5555555555555556
\* median in-degree: 2
\* max in-degree: 3
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(Server) /\ Cardinality(Server) > 1
ASSUME A1 == Nil \notin Server
ASSUME A2 == (Leader # Follower) /\ (Leader # Candidate)
ASSUME A3 == (Follower # Candidate)
ASSUME A4 == Server = Server
ASSUME A5 == Quorum \subseteq SUBSET Server /\ {} \notin Quorum /\ Quorum # {} /\ \A s \in Server : {s} \notin Quorum
ASSUME A6 == MaxLogLen \in Nat
ASSUME A7 == MaxTerm \in Nat
USE A0,A1,A2,A3,A4,A5,A6,A7

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,UpdateTermAction)
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK' BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>5. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
  \* (TypeOK,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv28_8e53_R0_0_I1 /\ Inv1270_3acc_R0_0_I1 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv28_8e53_R0_0_I1 /\ Inv1270_3acc_R0_0_I1 /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,Inv28_8e53_R0_0_I1,Inv1270_3acc_R0_0_I1,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv28_8e53_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv20_42ac_R1_0_I0 /\ Inv28_8e53_R0_0_I1 /\ Next => Inv28_8e53_R0_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv28_8e53_R0_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv28_8e53_R0_0_I1 /\ RequestVoteAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,Inv10_2c32_R1_1_I1,RequestVoteAction,RequestVote,Inv28_8e53_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv28_8e53_R0_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv28_8e53_R0_0_I1 /\ UpdateTermAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv28_8e53_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv28_8e53_R0_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv28_8e53_R0_0_I1 /\ BecomeLeaderAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv28_8e53_R0_0_I1
  \* (Inv28_8e53_R0_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv28_8e53_R0_0_I1 /\ ClientRequestAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv28_8e53_R0_0_I1
  \* (Inv28_8e53_R0_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv28_8e53_R0_0_I1 /\ AppendEntriesAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv28_8e53_R0_0_I1
  \* (Inv28_8e53_R0_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv28_8e53_R0_0_I1 /\ HandleRequestVoteRequestAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv28_8e53_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv28_8e53_R0_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv20_42ac_R1_0_I0 /\ Inv28_8e53_R0_0_I1 /\ HandleRequestVoteResponseAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,Inv20_42ac_R1_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv28_8e53_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv28_8e53_R0_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv28_8e53_R0_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv28_8e53_R0_0_I1
  \* (Inv28_8e53_R0_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv28_8e53_R0_0_I1 /\ HandleAppendEntriesResponseAction => Inv28_8e53_R0_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv28_8e53_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv20_42ac_R1_0_I0
THEOREM L_3 == TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv11_e30e_R3_0_I1 /\ Inv3_82b3_R3_1_I0 /\ Inv20_42ac_R1_0_I0 /\ Next => Inv20_42ac_R1_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv20_42ac_R1_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv20_42ac_R1_0_I0 /\ RequestVoteAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,Inv6_f533_R3_2_I0,RequestVoteAction,RequestVote,Inv20_42ac_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv20_42ac_R1_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv20_42ac_R1_0_I0 /\ UpdateTermAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv20_42ac_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv20_42ac_R1_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv20_42ac_R1_0_I0 /\ BecomeLeaderAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv20_42ac_R1_0_I0
  \* (Inv20_42ac_R1_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv20_42ac_R1_0_I0 /\ ClientRequestAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv20_42ac_R1_0_I0
  \* (Inv20_42ac_R1_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv20_42ac_R1_0_I0 /\ AppendEntriesAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv20_42ac_R1_0_I0
  \* (Inv20_42ac_R1_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_e30e_R3_0_I1 /\ Inv20_42ac_R1_0_I0 /\ HandleRequestVoteRequestAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,Inv11_e30e_R3_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv20_42ac_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv20_42ac_R1_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv3_82b3_R3_1_I0 /\ Inv20_42ac_R1_0_I0 /\ HandleRequestVoteResponseAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv20_42ac_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv20_42ac_R1_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv20_42ac_R1_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv20_42ac_R1_0_I0
  \* (Inv20_42ac_R1_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv20_42ac_R1_0_I0 /\ HandleAppendEntriesResponseAction => Inv20_42ac_R1_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv20_42ac_R1_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_e30e_R3_0_I1
THEOREM L_4 == TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv10_2c32_R1_1_I1 /\ Inv5_3715_R5_0_I0 /\ Inv11_e30e_R3_0_I1 /\ Next => Inv11_e30e_R3_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_e30e_R3_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv11_e30e_R3_0_I1 /\ RequestVoteAction => Inv11_e30e_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv10_2c32_R1_1_I1,
                        Inv11_e30e_R3_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv11_e30e_R3_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv10_2c32_R1_1_I1,RequestVoteAction,RequestVote,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_e30e_R3_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv11_e30e_R3_0_I1 /\ UpdateTermAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_e30e_R3_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_e30e_R3_0_I1 /\ BecomeLeaderAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_e30e_R3_0_I1 /\ ClientRequestAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_e30e_R3_0_I1 /\ AppendEntriesAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_e30e_R3_0_I1 /\ HandleRequestVoteRequestAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_e30e_R3_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_e30e_R3_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_3715_R5_0_I0 /\ Inv11_e30e_R3_0_I1 /\ HandleRequestVoteResponseAction => Inv11_e30e_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv5_3715_R5_0_I0,
                        Inv11_e30e_R3_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF HandleRequestVoteResponseAction, Inv11_e30e_R3_0_I1
    <2> QED
      BY DEF TypeOK,Inv5_3715_R5_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_e30e_R3_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_e30e_R3_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11_e30e_R3_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_e30e_R3_0_I1
  \* (Inv11_e30e_R3_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_e30e_R3_0_I1 /\ HandleAppendEntriesResponseAction => Inv11_e30e_R3_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_e30e_R3_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_3715_R5_0_I0
THEOREM L_5 == TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv6_f533_R3_2_I0 /\ Inv5_3715_R5_0_I0 /\ Next => Inv5_3715_R5_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_3715_R5_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv5_3715_R5_0_I0 /\ RequestVoteAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,Inv6_f533_R3_2_I0,RequestVoteAction,RequestVote,Inv5_3715_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_3715_R5_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv5_3715_R5_0_I0 /\ UpdateTermAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,Inv6_f533_R3_2_I0,UpdateTermAction,UpdateTerm,Inv5_3715_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_3715_R5_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5_3715_R5_0_I0 /\ BecomeLeaderAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5_3715_R5_0_I0
  \* (Inv5_3715_R5_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_3715_R5_0_I0 /\ ClientRequestAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_3715_R5_0_I0
  \* (Inv5_3715_R5_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_3715_R5_0_I0 /\ AppendEntriesAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_3715_R5_0_I0
  \* (Inv5_3715_R5_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_3715_R5_0_I0 /\ HandleRequestVoteRequestAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_3715_R5_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_3715_R5_0_I0 /\ HandleRequestVoteResponseAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_3715_R5_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_3715_R5_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_3715_R5_0_I0
  \* (Inv5_3715_R5_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_3715_R5_0_I0 /\ HandleAppendEntriesResponseAction => Inv5_3715_R5_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_3715_R5_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6_f533_R3_2_I0
THEOREM L_6 == TypeOK /\ Inv6_f533_R3_2_I0 /\ Next => Inv6_f533_R3_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_f533_R3_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_f533_R3_2_I0 /\ RequestVoteAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_f533_R3_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_f533_R3_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_f533_R3_2_I0 /\ UpdateTermAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_f533_R3_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_f533_R3_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_f533_R3_2_I0 /\ BecomeLeaderAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_f533_R3_2_I0
  \* (Inv6_f533_R3_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_f533_R3_2_I0 /\ ClientRequestAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_f533_R3_2_I0
  \* (Inv6_f533_R3_2_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv6_f533_R3_2_I0 /\ AppendEntriesAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_f533_R3_2_I0
  \* (Inv6_f533_R3_2_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_f533_R3_2_I0 /\ HandleRequestVoteRequestAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_f533_R3_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_f533_R3_2_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_f533_R3_2_I0 /\ HandleRequestVoteResponseAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_f533_R3_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_f533_R3_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_f533_R3_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_f533_R3_2_I0
  \* (Inv6_f533_R3_2_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6_f533_R3_2_I0 /\ HandleAppendEntriesResponseAction => Inv6_f533_R3_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_f533_R3_2_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv10_2c32_R1_1_I1
THEOREM L_7 == TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv10_2c32_R1_1_I1 /\ Next => Inv10_2c32_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_2c32_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_2c32_R1_1_I1 /\ RequestVoteAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_2c32_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_2c32_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_2c32_R1_1_I1 /\ UpdateTermAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_2c32_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_2c32_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_2c32_R1_1_I1 /\ BecomeLeaderAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_2c32_R1_1_I1
  \* (Inv10_2c32_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_2c32_R1_1_I1 /\ ClientRequestAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_2c32_R1_1_I1
  \* (Inv10_2c32_R1_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv10_2c32_R1_1_I1 /\ AppendEntriesAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_2c32_R1_1_I1
  \* (Inv10_2c32_R1_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv10_2c32_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_2c32_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_2c32_R1_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_f533_R3_2_I0 /\ Inv10_2c32_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,Inv6_f533_R3_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_2c32_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_2c32_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10_2c32_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_2c32_R1_1_I1
  \* (Inv10_2c32_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10_2c32_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_2c32_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_2c32_R1_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3_82b3_R3_1_I0
THEOREM L_8 == TypeOK /\ Inv5_3715_R5_0_I0 /\ Inv3_82b3_R3_1_I0 /\ Next => Inv3_82b3_R3_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_82b3_R3_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_82b3_R3_1_I0 /\ RequestVoteAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_82b3_R3_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_82b3_R3_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_82b3_R3_1_I0 /\ UpdateTermAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_82b3_R3_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_82b3_R3_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_82b3_R3_1_I0 /\ BecomeLeaderAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_82b3_R3_1_I0
  \* (Inv3_82b3_R3_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_82b3_R3_1_I0 /\ ClientRequestAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_82b3_R3_1_I0
  \* (Inv3_82b3_R3_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv3_82b3_R3_1_I0 /\ AppendEntriesAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_82b3_R3_1_I0
  \* (Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_3715_R5_0_I0 /\ Inv3_82b3_R3_1_I0 /\ HandleRequestVoteRequestAction => Inv3_82b3_R3_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv5_3715_R5_0_I0,
                        Inv3_82b3_R3_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv3_82b3_R3_1_I0
    <2> QED
      BY DEF TypeOK,Inv5_3715_R5_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_82b3_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_82b3_R3_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv3_82b3_R3_1_I0 /\ HandleRequestVoteResponseAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_82b3_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_82b3_R3_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv3_82b3_R3_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_82b3_R3_1_I0
  \* (Inv3_82b3_R3_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv3_82b3_R3_1_I0 /\ HandleAppendEntriesResponseAction => Inv3_82b3_R3_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_82b3_R3_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1270_3acc_R0_0_I1
THEOREM L_9 == TypeOK /\ Inv1270_3acc_R0_0_I1 /\ Next => Inv1270_3acc_R0_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1270_3acc_R0_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ RequestVoteAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1270_3acc_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1270_3acc_R0_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ UpdateTermAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1270_3acc_R0_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1270_3acc_R0_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ BecomeLeaderAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1270_3acc_R0_0_I1
  \* (Inv1270_3acc_R0_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ ClientRequestAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1270_3acc_R0_0_I1
  \* (Inv1270_3acc_R0_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ AppendEntriesAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1270_3acc_R0_0_I1
  \* (Inv1270_3acc_R0_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ HandleRequestVoteRequestAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1270_3acc_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1270_3acc_R0_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ HandleRequestVoteResponseAction => Inv1270_3acc_R0_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv1270_3acc_R0_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv1270_3acc_R0_0_I1
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1270_3acc_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1270_3acc_R0_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1270_3acc_R0_0_I1
  \* (Inv1270_3acc_R0_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ HandleAppendEntriesResponseAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1270_3acc_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal
    <1>2. Init => Inv28_8e53_R0_0_I1 BY DEF Init, Inv28_8e53_R0_0_I1, IndGlobal
    <1>3. Init => Inv20_42ac_R1_0_I0 BY DEF Init, Inv20_42ac_R1_0_I0, IndGlobal
    <1>4. Init => Inv11_e30e_R3_0_I1 BY DEF Init, Inv11_e30e_R3_0_I1, IndGlobal
    <1>5. Init => Inv5_3715_R5_0_I0 BY DEF Init, Inv5_3715_R5_0_I0, IndGlobal
    <1>6. Init => Inv6_f533_R3_2_I0 BY DEF Init, Inv6_f533_R3_2_I0, IndGlobal
    <1>7. Init => Inv10_2c32_R1_1_I1 BY DEF Init, Inv10_2c32_R1_1_I1, IndGlobal
    <1>8. Init => Inv3_82b3_R3_1_I0 BY DEF Init, Inv3_82b3_R3_1_I0, IndGlobal
    <1>9. Init => Inv1270_3acc_R0_0_I1 BY DEF Init, Inv1270_3acc_R0_0_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9 DEF Next, IndGlobal
================