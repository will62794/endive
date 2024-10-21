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
Inv11_e30e_R3_0_I1 == \A VARI \in Server : (state[VARI] # Follower) => (\A t \in votesGranted[VARI] : currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI ) 
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


\*LEMMA Inv11_e30e_R3_0_I1_alt <=> Inv11_e30e_R3_0_I1 
\* <1> QED BY TypeOK DEF Inv11_e30e_R3_0_I1_alt,Inv11_e30e_R3_0_I1, TypeOK


\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RequestVoteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY FS_Singleton, FS_Difference, FS_Union DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,LastTerm
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,UpdateTermAction)
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK' BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK' BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>5. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ AppendEntriesAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK, AppendEntriesRequestType, Min
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,LastTerm
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK,LogOk,CanAppend
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
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
  <1>3. TypeOK /\ Inv28_8e53_R0_0_I1 /\ Inv1270_3acc_R0_0_I1 /\ Safety /\ BecomeLeaderAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv28_8e53_R0_0_I1,
                        Inv1270_3acc_R0_0_I1,
                        Safety,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i)
                 PROVE  Safety'
      BY DEF BecomeLeaderAction
    <2> QED
      BY StaticQuorumsOverlap DEF TypeOK,Inv28_8e53_R0_0_I1,Inv1270_3acc_R0_0_I1,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
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
    <2> SUFFICES ASSUME TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv11_e30e_R3_0_I1 /\ RequestVoteAction,
                        NEW VARI \in Server',
                        (state[VARI] # Follower)',
                        NEW t \in (votesGranted[VARI])',
                        (currentTerm[t] = currentTerm[VARI])'
                 PROVE  (votedFor[t] = VARI)'
      BY DEF Inv11_e30e_R3_0_I1
    <2> QED
      <3> SUFFICES ASSUME NEW i \in Server,
                          RequestVote(i)
                   PROVE  (votedFor[t] = VARI)'
        BY DEF RequestVoteAction
      <3>1 CASE VARI = t
           BY <3>1 , FS_Singleton DEF LastTerm,TypeOK,Inv10_2c32_R1_1_I1,RequestVoteAction,RequestVote,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      <3>2 CASE VARI # t
           BY <3>2 , FS_Singleton DEF LastTerm,TypeOK,Inv10_2c32_R1_1_I1,RequestVoteAction,RequestVote,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
            
      <3> QED
        BY <3>1, <3>2 DEF LastTerm,TypeOK,Inv10_2c32_R1_1_I1,RequestVoteAction,RequestVote,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
    
  \* (Inv11_e30e_R3_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_2c32_R1_1_I1 /\ Inv11_e30e_R3_0_I1 /\ UpdateTermAction => Inv11_e30e_R3_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv10_2c32_R1_1_I1,
                        Inv11_e30e_R3_0_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m.mterm, m.mdest),
                        NEW VARI \in Server',
                        (state[VARI] # Follower)',
                        NEW t \in (votesGranted[VARI])',
                        (currentTerm[t] = currentTerm[VARI])'
                 PROVE  (votedFor[t] = VARI)'
      BY DEF Inv11_e30e_R3_0_I1, UpdateTermAction
   <2>1 CASE VARI = t
      BY <2>1 DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
   <2>2 CASE VARI # t /\ m.mdest # t 
      BY <2>2, FS_Singleton DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType    
    <2>3 CASE VARI # t /\ m.mdest = t /\ currentTerm[t] = currentTerm[VARI]
      BY <2>3, FS_Singleton DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType    
    <2>4 CASE VARI # t /\ m.mdest = t /\ currentTerm[t] > currentTerm[VARI]
      BY <2>4, FS_Singleton DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType    
    <2>5 CASE VARI # t /\ m.mdest = t /\ currentTerm[t] < currentTerm[VARI]
      BY <2>4, FS_Singleton DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType    
                
    <2> QED
      BY <2>1,<2>2 DEF TypeOK,Inv10_2c32_R1_1_I1,UpdateTermAction,UpdateTerm,Inv11_e30e_R3_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
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
                        NEW VARI \in Server',
                        (state[VARI] # Follower)',
                        NEW t \in (votesGranted[VARI])',
                        (currentTerm[t] = currentTerm[VARI])'
                 PROVE  (votedFor[t] = VARI)'
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
    <2>1. CASE m.mterm # currentTerm[m.mdest]
          BY <2>1 DEF TypeOK,Inv5_3715_R5_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_82b3_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
          BY <2>2 DEF TypeOK,Inv5_3715_R5_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_82b3_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3,<3>1 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
                BY <2>3,<3>2 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
                BY <2>3,<3>3 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>4 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY <4>1, <2>3,<3>4 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>5 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED BY <4>1, <2>3,<3>5 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ ~mi.mvoteGranted /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>2. votedFor[m.mdest] = mi.mdest
                BY <2>3,<3>6 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>3. QED BY <2>3,<3>6 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>7. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ mi.mvoteGranted 
                                         /\ mj.mvoteGranted /\ m.mdest = mi.msource 
                                         /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
                                         /\ votedFor[m.mdest] = Nil
            <4>2. votedFor'[m.mdest] = mi.mdest
                BY <2>3,<3>7 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. votedFor'[m.mdest] = mj.mdest
                BY <2>3,<3>7 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>4. QED BY <4>2, <4>3, <2>3,<3>7 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>8. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ mi.mvoteGranted 
                                         /\ mj.mvoteGranted /\ m.mdest = mi.msource 
                                         /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
                                         /\ votedFor[m.mdest] = m.msource
            <4>2. votedFor'[m.mdest] = mi.mdest
                BY <2>3,<3>8 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. votedFor'[m.mdest] = m.msource
                BY <2>3,<3>8 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>4. mi.mdest = m.msource
                BY <2>3,<3>8 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>5. currentTerm[mj.msource] = mj.mterm
                BY <2>3,<3>8 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>6. votedFor[mj.msource] = mj.mdest
              BY <2>3,<3>8, <4>5 DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
            <4>7. QED BY <4>2, <4>3, <4>4,<4>6, <2>3,<3>8 
            DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
                                            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6,<3>7,<3>8
                     DEF TypeOK,Inv3_82b3_R3_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_3715_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         
    <2> QED
      BY <2>1, <2>2, <2>3 DEF TypeOK,Inv5_3715_R5_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_82b3_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      ,TypeOK,Inv5_3715_R5_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_82b3_R3_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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
    <2>1. CASE m.mvoteGranted /\ state[VARI] # Leader
          BY <2>1 DEF TypeOK,Inv1270_3acc_R0_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mvoteGranted /\ state[VARI] = Leader
          BY AddingToQuorumRemainsQuorum, <2>2 DEF TypeOK,Inv1270_3acc_R0_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE ~m.mvoteGranted
          BY <2>2 DEF TypeOK,Inv1270_3acc_R0_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2> QED
      BY <2>1, <2>2, <2>3,
      StaticQuorumsOverlap, FS_Singleton, FS_Subset, FS_Union DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1270_3acc_R0_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1270_3acc_R0_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1270_3acc_R0_0_I1
  \* (Inv1270_3acc_R0_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1270_3acc_R0_0_I1 /\ HandleAppendEntriesResponseAction => Inv1270_3acc_R0_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1270_3acc_R0_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
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