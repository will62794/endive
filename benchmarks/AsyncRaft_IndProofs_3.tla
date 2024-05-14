--------------------------------- MODULE AsyncRaft_IndProofs_3 ---------------------------------
EXTENDS AsyncRaft,TLAPS,FiniteSetTheorems


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


\* Proof Graph Stats
\* ==================
\* seed: 3
\* num proof graph nodes: 12
\* num proof obligations: 144
Safety == H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
Inv30_R0_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv20_R0_1_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv2874_R0_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv18_R0_1_I1 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv10_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv0_R4_0_I2 == ( \A s,t \in Server : (/\ state[s] = Candidate /\ t \in votesGranted[s]) =>  /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s)
Inv3382_R4_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARJ] > currentTerm[VARI])) \/ ((votedFor[VARJ] = VARI) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI]))))
Inv864_R4_0_I2 == \A VARI \in Server : (votedFor[VARI] = VARI) \/ (~((state[VARI] = Leader)))
Inv1_R4_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv3_R6_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)
Inv31_R8_0_I1 == \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votedFor[VARJ] = VARJ))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv30_R0_0_I0
  /\ Inv18_R0_1_I1
  /\ Inv10_R1_1_I1
  /\ Inv20_R0_1_I1
  /\ Inv0_R4_0_I2
  /\ Inv3_R6_0_I0
  /\ Inv2874_R0_1_I1
  /\ Inv3382_R4_0_I2
  /\ Inv864_R4_0_I2
  /\ Inv31_R8_0_I1
  /\ Inv1_R4_1_I0


\* mean in-degree: 2.4166666666666665
\* median in-degree: 2
\* max in-degree: 9
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
  \* (TypeOK,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ TypeOK /\ AdvanceCommitIndexAction => TypeOK' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>6. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ TypeOK /\ RejectAppendEntriesRequestAction => TypeOK' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,TypeOK
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
  \* (TypeOK,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestLearnCommitAction => TypeOK' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,TypeOK
  \* (TypeOK,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv30_R0_0_I0 /\ Inv30_R0_0_I0 /\ Inv20_R0_1_I1 /\ Inv2874_R0_1_I1 /\ Inv18_R0_1_I1 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7,
  StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Safety,RequestVoteAction)
  <1> USE DEF H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' 
    <2> SUFFICES ASSUME TypeOK,
                        Safety,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i)
                 PROVE  Safety'
      BY DEF RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv30_R0_0_I0 /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,Inv30_R0_0_I0,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Safety /\ AdvanceCommitIndexAction => Safety' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Safety,H_OnePrimaryPerTerm
  \* (Safety,AppendEntriesAction)
  <1>6. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv30_R0_0_I0 /\ Inv20_R0_1_I1 /\ Inv2874_R0_1_I1 /\ Inv18_R0_1_I1 /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,Inv30_R0_0_I0,Inv20_R0_1_I1,Inv2874_R0_1_I1,Inv18_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Safety /\ RejectAppendEntriesRequestAction => Safety' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Safety /\ AcceptAppendEntriesRequestLearnCommitAction => Safety' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv30_R0_0_I0
THEOREM L_2 == TypeOK /\ Inv10_R1_1_I1 /\ Inv2874_R0_1_I1 /\ Inv18_R0_1_I1 /\ Inv30_R0_0_I0 /\ Next => Inv30_R0_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv30_R0_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R1_1_I1 /\ Inv2874_R0_1_I1 /\ Inv30_R0_0_I0 /\ RequestVoteAction => Inv30_R0_0_I0' BY DEF TypeOK,Inv10_R1_1_I1,Inv2874_R0_1_I1,RequestVoteAction,RequestVote,Inv30_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv30_R0_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv30_R0_0_I0 /\ UpdateTermAction => Inv30_R0_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv30_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv30_R0_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv30_R0_0_I0 /\ BecomeLeaderAction => Inv30_R0_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv30_R0_0_I0 /\ ClientRequestAction => Inv30_R0_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv30_R0_0_I0 /\ AdvanceCommitIndexAction => Inv30_R0_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv30_R0_0_I0 /\ AppendEntriesAction => Inv30_R0_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv30_R0_0_I0 /\ HandleRequestVoteRequestAction => Inv30_R0_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv30_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv30_R0_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv18_R0_1_I1 /\ Inv30_R0_0_I0 /\ HandleRequestVoteResponseAction => Inv30_R0_0_I0' BY DEF TypeOK,Inv18_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv30_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv30_R0_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv30_R0_0_I0 /\ RejectAppendEntriesRequestAction => Inv30_R0_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv30_R0_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv30_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv30_R0_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv30_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv30_R0_0_I0 /\ HandleAppendEntriesResponseAction => Inv30_R0_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv30_R0_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv18_R0_1_I1
THEOREM L_3 == TypeOK /\ Inv20_R0_1_I1 /\ Inv10_R1_1_I1 /\ Inv0_R4_0_I2 /\ Inv2874_R0_1_I1 /\ Inv3382_R4_0_I2 /\ Inv20_R0_1_I1 /\ Inv864_R4_0_I2 /\ Inv30_R0_0_I0 /\ Inv1_R4_1_I0 /\ Inv18_R0_1_I1 /\ Next => Inv18_R0_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv18_R0_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv20_R0_1_I1 /\ Inv18_R0_1_I1 /\ RequestVoteAction => Inv18_R0_1_I1' BY DEF TypeOK,Inv20_R0_1_I1,RequestVoteAction,RequestVote,Inv18_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_R0_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv18_R0_1_I1 /\ UpdateTermAction => Inv18_R0_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv18_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_R0_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv18_R0_1_I1 /\ BecomeLeaderAction => Inv18_R0_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv18_R0_1_I1 /\ ClientRequestAction => Inv18_R0_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv18_R0_1_I1 /\ AdvanceCommitIndexAction => Inv18_R0_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv18_R0_1_I1 /\ AppendEntriesAction => Inv18_R0_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R1_1_I1 /\ Inv0_R4_0_I2 /\ Inv2874_R0_1_I1 /\ Inv3382_R4_0_I2 /\ Inv20_R0_1_I1 /\ Inv864_R4_0_I2 /\ Inv30_R0_0_I0 /\ Inv18_R0_1_I1 /\ HandleRequestVoteRequestAction => Inv18_R0_1_I1' BY DEF TypeOK,Inv10_R1_1_I1,Inv0_R4_0_I2,Inv2874_R0_1_I1,Inv3382_R4_0_I2,Inv20_R0_1_I1,Inv864_R4_0_I2,Inv30_R0_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv18_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_R0_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R4_1_I0 /\ Inv18_R0_1_I1 /\ HandleRequestVoteResponseAction => Inv18_R0_1_I1' BY DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv18_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_R0_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv18_R0_1_I1 /\ RejectAppendEntriesRequestAction => Inv18_R0_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv18_R0_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv18_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv18_R0_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv18_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv18_R0_1_I1
  \* (Inv18_R0_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv18_R0_1_I1 /\ HandleAppendEntriesResponseAction => Inv18_R0_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv18_R0_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R1_1_I1
THEOREM L_4 == TypeOK /\ Inv20_R0_1_I1 /\ Inv10_R1_1_I1 /\ Next => Inv10_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R1_1_I1 /\ RequestVoteAction => Inv10_R1_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R1_1_I1 /\ UpdateTermAction => Inv10_R1_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_R1_1_I1 /\ BecomeLeaderAction => Inv10_R1_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_R1_1_I1 /\ ClientRequestAction => Inv10_R1_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10_R1_1_I1 /\ AdvanceCommitIndexAction => Inv10_R1_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10_R1_1_I1 /\ AppendEntriesAction => Inv10_R1_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv10_R1_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv20_R0_1_I1 /\ Inv10_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv10_R1_1_I1' BY DEF TypeOK,Inv20_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv10_R1_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv20_R0_1_I1
THEOREM L_5 == TypeOK /\ Inv20_R0_1_I1 /\ Next => Inv20_R0_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv20_R0_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv20_R0_1_I1 /\ RequestVoteAction => Inv20_R0_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv20_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv20_R0_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv20_R0_1_I1 /\ UpdateTermAction => Inv20_R0_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv20_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv20_R0_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv20_R0_1_I1 /\ BecomeLeaderAction => Inv20_R0_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv20_R0_1_I1 /\ ClientRequestAction => Inv20_R0_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv20_R0_1_I1 /\ AdvanceCommitIndexAction => Inv20_R0_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv20_R0_1_I1 /\ AppendEntriesAction => Inv20_R0_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv20_R0_1_I1 /\ HandleRequestVoteRequestAction => Inv20_R0_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv20_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv20_R0_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv20_R0_1_I1 /\ HandleRequestVoteResponseAction => Inv20_R0_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv20_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv20_R0_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv20_R0_1_I1 /\ RejectAppendEntriesRequestAction => Inv20_R0_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv20_R0_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv20_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv20_R0_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv20_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv20_R0_1_I1
  \* (Inv20_R0_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv20_R0_1_I1 /\ HandleAppendEntriesResponseAction => Inv20_R0_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv20_R0_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv0_R4_0_I2
THEOREM L_6 == TypeOK /\ Inv10_R1_1_I1 /\ Inv10_R1_1_I1 /\ Inv3_R6_0_I0 /\ Inv0_R4_0_I2 /\ Next => Inv0_R4_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7, StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Inv0_R4_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R1_1_I1 /\ Inv0_R4_0_I2 /\ RequestVoteAction => Inv0_R4_0_I2' BY DEF TypeOK,Inv10_R1_1_I1,RequestVoteAction,RequestVote,Inv0_R4_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R4_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R1_1_I1 /\ Inv0_R4_0_I2 /\ UpdateTermAction => Inv0_R4_0_I2' BY DEF TypeOK,Inv10_R1_1_I1,UpdateTermAction,UpdateTerm,Inv0_R4_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R4_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_R4_0_I2 /\ BecomeLeaderAction => Inv0_R4_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_R4_0_I2 /\ ClientRequestAction => Inv0_R4_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv0_R4_0_I2 /\ AdvanceCommitIndexAction => Inv0_R4_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv0_R4_0_I2 /\ AppendEntriesAction => Inv0_R4_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv0_R4_0_I2 /\ HandleRequestVoteRequestAction => Inv0_R4_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R4_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R4_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R6_0_I0 /\ Inv0_R4_0_I2 /\ HandleRequestVoteResponseAction => Inv0_R4_0_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv3_R6_0_I0 /\ Inv0_R4_0_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW s \in Server', NEW t \in Server',
                        (/\ state[s] = Candidate /\ t \in votesGranted[s])'
                 PROVE  (/\ currentTerm[t] = currentTerm[s] => votedFor[t] = s)'
      BY DEF Inv0_R4_0_I2, HandleRequestVoteResponseAction
    <2>1. (currentTerm[t] = currentTerm[s] => votedFor[t] = s)'
      <3> SUFFICES ASSUME (currentTerm[t] = currentTerm[s])'
                   PROVE  (votedFor[t] = s)'
        OBVIOUS
      <3>1. CASE m.mvoteGranted /\ m.mdest # s
              BY <3>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R4_0_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      <3>2. CASE m.mvoteGranted /\ m.mdest = s
        <4>1. votedFor[t] = m.mdest
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R4_0_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        <4>2. QED 
                BY <3>2,<4>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R4_0_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
      <3>3. CASE ~m.mvoteGranted
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R4_0_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
      <3> QED
        BY <3>1,<3>2,<3>3,FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R4_0_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
\*      BY DEF TypeOK,Inv3_R6_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_R4_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. QED
      BY <2>1
  \* (Inv0_R4_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv0_R4_0_I2 /\ RejectAppendEntriesRequestAction => Inv0_R4_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv0_R4_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv0_R4_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv0_R4_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv0_R4_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv0_R4_0_I2
  \* (Inv0_R4_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv0_R4_0_I2 /\ HandleAppendEntriesResponseAction => Inv0_R4_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_R4_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3_R6_0_I0
THEOREM L_7 == TypeOK /\ Inv20_R0_1_I1 /\ Inv20_R0_1_I1 /\ Inv3_R6_0_I0 /\ Next => Inv3_R6_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_R6_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv20_R0_1_I1 /\ Inv3_R6_0_I0 /\ RequestVoteAction => Inv3_R6_0_I0' BY DEF TypeOK,Inv20_R0_1_I1,RequestVoteAction,RequestVote,Inv3_R6_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R6_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv20_R0_1_I1 /\ Inv3_R6_0_I0 /\ UpdateTermAction => Inv3_R6_0_I0' BY DEF TypeOK,Inv20_R0_1_I1,UpdateTermAction,UpdateTerm,Inv3_R6_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R6_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_R6_0_I0 /\ BecomeLeaderAction => Inv3_R6_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_R6_0_I0 /\ ClientRequestAction => Inv3_R6_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv3_R6_0_I0 /\ AdvanceCommitIndexAction => Inv3_R6_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv3_R6_0_I0 /\ AppendEntriesAction => Inv3_R6_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv3_R6_0_I0 /\ HandleRequestVoteRequestAction => Inv3_R6_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R6_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R6_0_I0 /\ HandleRequestVoteResponseAction => Inv3_R6_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R6_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv3_R6_0_I0 /\ RejectAppendEntriesRequestAction => Inv3_R6_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv3_R6_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_R6_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv3_R6_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv3_R6_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv3_R6_0_I0
  \* (Inv3_R6_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv3_R6_0_I0 /\ HandleAppendEntriesResponseAction => Inv3_R6_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_R6_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2874_R0_1_I1
THEOREM L_8 == TypeOK /\ Inv2874_R0_1_I1 /\ Next => Inv2874_R0_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7, StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Inv2874_R0_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv2874_R0_1_I1 /\ RequestVoteAction => Inv2874_R0_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv2874_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2874_R0_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv2874_R0_1_I1 /\ UpdateTermAction => Inv2874_R0_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv2874_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2874_R0_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2874_R0_1_I1 /\ BecomeLeaderAction => Inv2874_R0_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv2874_R0_1_I1 /\ ClientRequestAction => Inv2874_R0_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv2874_R0_1_I1 /\ AdvanceCommitIndexAction => Inv2874_R0_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv2874_R0_1_I1 /\ AppendEntriesAction => Inv2874_R0_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv2874_R0_1_I1 /\ HandleRequestVoteRequestAction => Inv2874_R0_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2874_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2874_R0_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv2874_R0_1_I1 /\ HandleRequestVoteResponseAction => Inv2874_R0_1_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv2874_R0_1_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv2874_R0_1_I1
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2874_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2874_R0_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv2874_R0_1_I1 /\ RejectAppendEntriesRequestAction => Inv2874_R0_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv2874_R0_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv2874_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv2874_R0_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv2874_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv2874_R0_1_I1
  \* (Inv2874_R0_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv2874_R0_1_I1 /\ HandleAppendEntriesResponseAction => Inv2874_R0_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2874_R0_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3382_R4_0_I2
THEOREM L_9 == TypeOK /\ Inv10_R1_1_I1 /\ Inv10_R1_1_I1 /\ Inv20_R0_1_I1 /\ Inv3_R6_0_I0 /\ Inv3382_R4_0_I2 /\ Next => Inv3382_R4_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3382_R4_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R1_1_I1 /\ Inv3382_R4_0_I2 /\ RequestVoteAction => Inv3382_R4_0_I2' BY DEF TypeOK,Inv10_R1_1_I1,RequestVoteAction,RequestVote,Inv3382_R4_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3382_R4_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R1_1_I1 /\ Inv3382_R4_0_I2 /\ UpdateTermAction => Inv3382_R4_0_I2' BY DEF TypeOK,Inv10_R1_1_I1,UpdateTermAction,UpdateTerm,Inv3382_R4_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3382_R4_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3382_R4_0_I2 /\ BecomeLeaderAction => Inv3382_R4_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv3382_R4_0_I2 /\ ClientRequestAction => Inv3382_R4_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv3382_R4_0_I2 /\ AdvanceCommitIndexAction => Inv3382_R4_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv3382_R4_0_I2 /\ AppendEntriesAction => Inv3382_R4_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv3382_R4_0_I2 /\ HandleRequestVoteRequestAction => Inv3382_R4_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3382_R4_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3382_R4_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv20_R0_1_I1 /\ Inv3_R6_0_I0 /\ Inv3382_R4_0_I2 /\ HandleRequestVoteResponseAction => Inv3382_R4_0_I2' BY DEF TypeOK,Inv20_R0_1_I1,Inv3_R6_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3382_R4_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3382_R4_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv3382_R4_0_I2 /\ RejectAppendEntriesRequestAction => Inv3382_R4_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv3382_R4_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv3382_R4_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv3382_R4_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv3382_R4_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv3382_R4_0_I2
  \* (Inv3382_R4_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv3382_R4_0_I2 /\ HandleAppendEntriesResponseAction => Inv3382_R4_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3382_R4_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv864_R4_0_I2
THEOREM L_10 == TypeOK /\ Inv31_R8_0_I1 /\ Inv864_R4_0_I2 /\ Next => Inv864_R4_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv864_R4_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv864_R4_0_I2 /\ RequestVoteAction => Inv864_R4_0_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv864_R4_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv864_R4_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv864_R4_0_I2 /\ UpdateTermAction => Inv864_R4_0_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv864_R4_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv864_R4_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_R8_0_I1 /\ Inv864_R4_0_I2 /\ BecomeLeaderAction => Inv864_R4_0_I2' BY DEF TypeOK,Inv31_R8_0_I1,BecomeLeaderAction,BecomeLeader,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv864_R4_0_I2 /\ ClientRequestAction => Inv864_R4_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv864_R4_0_I2 /\ AdvanceCommitIndexAction => Inv864_R4_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv864_R4_0_I2 /\ AppendEntriesAction => Inv864_R4_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv864_R4_0_I2 /\ HandleRequestVoteRequestAction => Inv864_R4_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv864_R4_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv864_R4_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv864_R4_0_I2 /\ HandleRequestVoteResponseAction => Inv864_R4_0_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv864_R4_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv864_R4_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv864_R4_0_I2 /\ RejectAppendEntriesRequestAction => Inv864_R4_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv864_R4_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv864_R4_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv864_R4_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv864_R4_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv864_R4_0_I2
  \* (Inv864_R4_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv864_R4_0_I2 /\ HandleAppendEntriesResponseAction => Inv864_R4_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv864_R4_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv31_R8_0_I1
THEOREM L_11 == TypeOK /\ Inv31_R8_0_I1 /\ Next => Inv31_R8_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv31_R8_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv31_R8_0_I1 /\ RequestVoteAction => Inv31_R8_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv31_R8_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_R8_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv31_R8_0_I1 /\ UpdateTermAction => Inv31_R8_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv31_R8_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_R8_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_R8_0_I1 /\ BecomeLeaderAction => Inv31_R8_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv31_R8_0_I1 /\ ClientRequestAction => Inv31_R8_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv31_R8_0_I1 /\ AdvanceCommitIndexAction => Inv31_R8_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv31_R8_0_I1 /\ AppendEntriesAction => Inv31_R8_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv31_R8_0_I1 /\ HandleRequestVoteRequestAction => Inv31_R8_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv31_R8_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_R8_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv31_R8_0_I1 /\ HandleRequestVoteResponseAction => Inv31_R8_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv31_R8_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_R8_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv31_R8_0_I1 /\ RejectAppendEntriesRequestAction => Inv31_R8_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv31_R8_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv31_R8_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv31_R8_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv31_R8_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv31_R8_0_I1
  \* (Inv31_R8_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv31_R8_0_I1 /\ HandleAppendEntriesResponseAction => Inv31_R8_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv31_R8_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_R4_1_I0
THEOREM L_12 == TypeOK /\ Inv3_R6_0_I0 /\ Inv1_R4_1_I0 /\ Next => Inv1_R4_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7, StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Inv1_R4_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv1_R4_1_I0 /\ RequestVoteAction => Inv1_R4_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1_R4_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R4_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R4_1_I0 /\ UpdateTermAction => Inv1_R4_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1_R4_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R4_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1_R4_1_I0 /\ BecomeLeaderAction => Inv1_R4_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv1_R4_1_I0 /\ ClientRequestAction => Inv1_R4_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1_R4_1_I0 /\ AdvanceCommitIndexAction => Inv1_R4_1_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1_R4_1_I0 /\ AppendEntriesAction => Inv1_R4_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv3_R6_0_I0 /\ Inv1_R4_1_I0 /\ HandleRequestVoteRequestAction => Inv1_R4_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv3_R6_0_I0,
                        Inv1_R4_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv1_R4_1_I0
    <2>1. CASE m.mterm # currentTerm[m.mdest]
        BY <2>1 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
            BY <2>2 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3,<3>1 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
                BY <2>3,<3>2 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
                BY <2>3,<3>3 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>4 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY <4>1, <2>3,<3>4 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>5 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED BY <4>1, <2>3,<3>5 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>3. QED BY <3>6 DEF TypeOK,Inv1_R4_1_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R6_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6
    <2> QED
      BY <2>1, <2>2, <2>3  DEF TypeOK,Inv3_R6_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1_R4_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R4_1_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R4_1_I0 /\ HandleRequestVoteResponseAction => Inv1_R4_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1_R4_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R4_1_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1_R4_1_I0 /\ RejectAppendEntriesRequestAction => Inv1_R4_1_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1_R4_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv1_R4_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1_R4_1_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1_R4_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1_R4_1_I0
  \* (Inv1_R4_1_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1_R4_1_I0 /\ HandleAppendEntriesResponseAction => Inv1_R4_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1_R4_1_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
    <1>2. Init => Inv30_R0_0_I0 BY DEF Init, Inv30_R0_0_I0, IndGlobal
    <1>3. Init => Inv18_R0_1_I1 BY DEF Init, Inv18_R0_1_I1, IndGlobal
    <1>4. Init => Inv10_R1_1_I1 BY DEF Init, Inv10_R1_1_I1, IndGlobal
    <1>5. Init => Inv20_R0_1_I1 BY DEF Init, Inv20_R0_1_I1, IndGlobal
    <1>6. Init => Inv0_R4_0_I2 BY DEF Init, Inv0_R4_0_I2, IndGlobal
    <1>7. Init => Inv3_R6_0_I0 BY DEF Init, Inv3_R6_0_I0, IndGlobal
    <1>8. Init => Inv2874_R0_1_I1 BY DEF Init, Inv2874_R0_1_I1, IndGlobal
    <1>9. Init => Inv3382_R4_0_I2 BY DEF Init, Inv3382_R4_0_I2, IndGlobal
    <1>10. Init => Inv864_R4_0_I2 BY DEF Init, Inv864_R4_0_I2, IndGlobal
    <1>11. Init => Inv31_R8_0_I1 BY DEF Init, Inv31_R8_0_I1, IndGlobal
    <1>12. Init => Inv1_R4_1_I0 BY DEF Init, Inv1_R4_1_I0, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12 DEF Next, IndGlobal

====