--------------------------------- MODULE AsyncRaft_IndProofs_2 ---------------------------------
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
\* seed: 2
\* num proof graph nodes: 11
\* num proof obligations: 132
Safety == H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
Inv30_R0_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv15_R0_1_I2 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv12044_R0_1_I2 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))
Inv1902_R0_1_I2 == \A VARI \in Server : (VARI \in votesGranted[VARI]) \/ (~((state[VARI] = Leader)))
Inv17_R0_1_I2 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv10_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv9_R2_0_I0 == (\A s \in Server : state[s] \in {Candidate,Leader} =>  (\A t \in votesGranted[s] :  /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s ))
Inv3_R2_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv3_R4_0_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((VARI \in votesGranted[VARI]))
Inv4_R7_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv30_R0_0_I0
  /\ Inv15_R0_1_I2
  /\ Inv9_R2_0_I0
  /\ Inv4_R7_0_I0
  /\ Inv17_R0_1_I2
  /\ Inv10_R1_1_I1
  /\ Inv3_R2_1_I0
  /\ Inv1902_R0_1_I2
  /\ Inv3_R4_0_I1
  /\ Inv12044_R0_1_I2


\* mean in-degree: 1.9090909090909092
\* median in-degree: 1
\* max in-degree: 6
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
THEOREM L_1 == TypeOK /\ Inv30_R0_0_I0 /\ Inv30_R0_0_I0 /\ Inv15_R0_1_I2 /\ Inv12044_R0_1_I2 /\ Inv1902_R0_1_I2 /\ Inv17_R0_1_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  <1>. USE DEF H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
  <1> USE A0,A1,A2,A3,A4,A5,A6,A7,
        StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Safety,RequestVoteAction)
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
  <1>8. TypeOK /\ Inv30_R0_0_I0 /\ Inv15_R0_1_I2 /\ Inv12044_R0_1_I2 /\ Inv1902_R0_1_I2 /\ Inv17_R0_1_I2 /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,Inv30_R0_0_I0,Inv15_R0_1_I2,Inv12044_R0_1_I2,Inv1902_R0_1_I2,Inv17_R0_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
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
THEOREM L_2 == TypeOK /\ Inv1902_R0_1_I2 /\ Inv10_R1_1_I1 /\ Inv12044_R0_1_I2 /\ Inv15_R0_1_I2 /\ Inv30_R0_0_I0 /\ Next => Inv30_R0_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv30_R0_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv1902_R0_1_I2 /\ Inv10_R1_1_I1 /\ Inv12044_R0_1_I2 /\ Inv30_R0_0_I0 /\ RequestVoteAction => Inv30_R0_0_I0' BY DEF TypeOK,Inv1902_R0_1_I2,Inv10_R1_1_I1,Inv12044_R0_1_I2,RequestVoteAction,RequestVote,Inv30_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
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
  <1>8. TypeOK /\ Inv15_R0_1_I2 /\ Inv30_R0_0_I0 /\ HandleRequestVoteResponseAction => Inv30_R0_0_I0' BY DEF TypeOK,Inv15_R0_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv30_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv30_R0_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv30_R0_0_I0 /\ RejectAppendEntriesRequestAction => Inv30_R0_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv30_R0_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv30_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv30_R0_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv30_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv30_R0_0_I0
  \* (Inv30_R0_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv30_R0_0_I0 /\ HandleAppendEntriesResponseAction => Inv30_R0_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv30_R0_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv15_R0_1_I2
THEOREM L_3 == TypeOK /\ Inv17_R0_1_I2 /\ Inv9_R2_0_I0 /\ Inv3_R2_1_I0 /\ Inv15_R0_1_I2 /\ Next => Inv15_R0_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv15_R0_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv17_R0_1_I2 /\ Inv15_R0_1_I2 /\ RequestVoteAction => Inv15_R0_1_I2' BY DEF TypeOK,Inv17_R0_1_I2,RequestVoteAction,RequestVote,Inv15_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_R0_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv15_R0_1_I2 /\ UpdateTermAction => Inv15_R0_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv15_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_R0_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv15_R0_1_I2 /\ BecomeLeaderAction => Inv15_R0_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv15_R0_1_I2 /\ ClientRequestAction => Inv15_R0_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv15_R0_1_I2 /\ AdvanceCommitIndexAction => Inv15_R0_1_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv15_R0_1_I2 /\ AppendEntriesAction => Inv15_R0_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv9_R2_0_I0 /\ Inv15_R0_1_I2 /\ HandleRequestVoteRequestAction => Inv15_R0_1_I2' BY DEF TypeOK,Inv9_R2_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv15_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_R0_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R2_1_I0 /\ Inv15_R0_1_I2 /\ HandleRequestVoteResponseAction => Inv15_R0_1_I2' BY DEF TypeOK,Inv3_R2_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv15_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_R0_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv15_R0_1_I2 /\ RejectAppendEntriesRequestAction => Inv15_R0_1_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv15_R0_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv15_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv15_R0_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv15_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv15_R0_1_I2
  \* (Inv15_R0_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv15_R0_1_I2 /\ HandleAppendEntriesResponseAction => Inv15_R0_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv15_R0_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv9_R2_0_I0
THEOREM L_4 == TypeOK /\ Inv10_R1_1_I1 /\ Inv10_R1_1_I1 /\ Inv4_R7_0_I0 /\ Inv9_R2_0_I0 /\ Next => Inv9_R2_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  <1> USE StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Intersection, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Inv9_R2_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R1_1_I1 /\ Inv9_R2_0_I0 /\ RequestVoteAction => Inv9_R2_0_I0' BY DEF TypeOK,Inv10_R1_1_I1,RequestVoteAction,RequestVote,Inv9_R2_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_R2_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R1_1_I1 /\ Inv9_R2_0_I0 /\ UpdateTermAction => Inv9_R2_0_I0' BY DEF TypeOK,Inv10_R1_1_I1,UpdateTermAction,UpdateTerm,Inv9_R2_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_R2_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_R2_0_I0 /\ BecomeLeaderAction => Inv9_R2_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_R2_0_I0 /\ ClientRequestAction => Inv9_R2_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv9_R2_0_I0 /\ AdvanceCommitIndexAction => Inv9_R2_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv9_R2_0_I0 /\ AppendEntriesAction => Inv9_R2_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv9_R2_0_I0 /\ HandleRequestVoteRequestAction => Inv9_R2_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_R2_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_R2_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv4_R7_0_I0 /\ Inv9_R2_0_I0 /\ HandleRequestVoteResponseAction => Inv9_R2_0_I0' 
    <2> SUFFICES ASSUME TypeOK /\ Inv4_R7_0_I0 /\ Inv9_R2_0_I0 /\ HandleRequestVoteResponseAction,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW s \in Server',
                        (state[s] \in {Candidate,Leader})',
                        NEW t \in (votesGranted[s])'
                 PROVE  (/\ currentTerm[t] = currentTerm[s] => votedFor[t] = s)'
      BY DEF HandleRequestVoteResponseAction, Inv9_R2_0_I0, Inv4_R7_0_I0
    <2>1. (currentTerm[t] = currentTerm[s] => votedFor[t] = s)'
      <3> SUFFICES ASSUME (currentTerm[t] = currentTerm[s])'
                   PROVE  (votedFor[t] = s)'
        OBVIOUS
      <3>1. CASE m.mvoteGranted /\ m.mdest # s
              BY <3>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_R2_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      <3>2. CASE m.mvoteGranted /\ m.mdest = s
        <4>1. votedFor[t] = m.mdest
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_R2_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        <4>2. QED 
                BY <3>2,<4>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_R2_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
      <3>3. CASE ~m.mvoteGranted
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_R2_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
      <3> QED
        BY <3>1,<3>2,<3>3,FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv9_R2_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
    <2>2. QED
      BY <2>1
  \* (Inv9_R2_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv9_R2_0_I0 /\ RejectAppendEntriesRequestAction => Inv9_R2_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv9_R2_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv9_R2_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv9_R2_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv9_R2_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv9_R2_0_I0
  \* (Inv9_R2_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv9_R2_0_I0 /\ HandleAppendEntriesResponseAction => Inv9_R2_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_R2_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4_R7_0_I0
THEOREM L_5 == TypeOK /\ Inv17_R0_1_I2 /\ Inv17_R0_1_I2 /\ Inv4_R7_0_I0 /\ Next => Inv4_R7_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4_R7_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv17_R0_1_I2 /\ Inv4_R7_0_I0 /\ RequestVoteAction => Inv4_R7_0_I0' BY DEF TypeOK,Inv17_R0_1_I2,RequestVoteAction,RequestVote,Inv4_R7_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_R7_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv17_R0_1_I2 /\ Inv4_R7_0_I0 /\ UpdateTermAction => Inv4_R7_0_I0' BY DEF TypeOK,Inv17_R0_1_I2,UpdateTermAction,UpdateTerm,Inv4_R7_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_R7_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_R7_0_I0 /\ BecomeLeaderAction => Inv4_R7_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv4_R7_0_I0 /\ ClientRequestAction => Inv4_R7_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv4_R7_0_I0 /\ AdvanceCommitIndexAction => Inv4_R7_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv4_R7_0_I0 /\ AppendEntriesAction => Inv4_R7_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv4_R7_0_I0 /\ HandleRequestVoteRequestAction => Inv4_R7_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_R7_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv4_R7_0_I0 /\ HandleRequestVoteResponseAction => Inv4_R7_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R7_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_R7_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv4_R7_0_I0 /\ RejectAppendEntriesRequestAction => Inv4_R7_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv4_R7_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv4_R7_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv4_R7_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv4_R7_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv4_R7_0_I0
  \* (Inv4_R7_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv4_R7_0_I0 /\ HandleAppendEntriesResponseAction => Inv4_R7_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_R7_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv17_R0_1_I2
THEOREM L_6 == TypeOK /\ Inv17_R0_1_I2 /\ Next => Inv17_R0_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv17_R0_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv17_R0_1_I2 /\ RequestVoteAction => Inv17_R0_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv17_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17_R0_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv17_R0_1_I2 /\ UpdateTermAction => Inv17_R0_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv17_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17_R0_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv17_R0_1_I2 /\ BecomeLeaderAction => Inv17_R0_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv17_R0_1_I2 /\ ClientRequestAction => Inv17_R0_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv17_R0_1_I2 /\ AdvanceCommitIndexAction => Inv17_R0_1_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv17_R0_1_I2 /\ AppendEntriesAction => Inv17_R0_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv17_R0_1_I2 /\ HandleRequestVoteRequestAction => Inv17_R0_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv17_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17_R0_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv17_R0_1_I2 /\ HandleRequestVoteResponseAction => Inv17_R0_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17_R0_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv17_R0_1_I2 /\ RejectAppendEntriesRequestAction => Inv17_R0_1_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv17_R0_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv17_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv17_R0_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv17_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv17_R0_1_I2
  \* (Inv17_R0_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv17_R0_1_I2 /\ HandleAppendEntriesResponseAction => Inv17_R0_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv17_R0_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R1_1_I1
THEOREM L_7 == TypeOK /\ Inv17_R0_1_I2 /\ Inv10_R1_1_I1 /\ Next => Inv10_R1_1_I1'
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
  <1>8. TypeOK /\ Inv17_R0_1_I2 /\ Inv10_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv10_R1_1_I1' BY DEF TypeOK,Inv17_R0_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv10_R1_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R1_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R1_1_I1
  \* (Inv10_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_R1_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3_R2_1_I0
THEOREM L_8 == TypeOK /\ Inv4_R7_0_I0 /\ Inv3_R2_1_I0 /\ Next => Inv3_R2_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  <1> USE StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Inv3_R2_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_R2_1_I0 /\ RequestVoteAction => Inv3_R2_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_R2_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R2_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_R2_1_I0 /\ UpdateTermAction => Inv3_R2_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_R2_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R2_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_R2_1_I0 /\ BecomeLeaderAction => Inv3_R2_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_R2_1_I0 /\ ClientRequestAction => Inv3_R2_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv3_R2_1_I0 /\ AdvanceCommitIndexAction => Inv3_R2_1_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv3_R2_1_I0 /\ AppendEntriesAction => Inv3_R2_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv4_R7_0_I0 /\ Inv3_R2_1_I0 /\ HandleRequestVoteRequestAction => Inv3_R2_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv4_R7_0_I0,
                        Inv3_R2_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv3_R2_1_I0
    <2>1. CASE m.mterm # currentTerm[m.mdest]
        BY <2>1 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
            BY <2>2 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3,<3>1 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
                BY <2>3,<3>2 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
                BY <2>3,<3>3 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>4 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY <4>1, <2>3,<3>4 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>5 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED BY <4>1, <2>3,<3>5 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>3. QED BY <3>6 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6
    <2> QED
      BY <2>1, <2>2, <2>3 DEF TypeOK,Inv4_R7_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R2_1_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R2_1_I0 /\ HandleRequestVoteResponseAction => Inv3_R2_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R2_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R2_1_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv3_R2_1_I0 /\ RejectAppendEntriesRequestAction => Inv3_R2_1_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv3_R2_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_R2_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv3_R2_1_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv3_R2_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv3_R2_1_I0
  \* (Inv3_R2_1_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv3_R2_1_I0 /\ HandleAppendEntriesResponseAction => Inv3_R2_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_R2_1_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1902_R0_1_I2
THEOREM L_9 == TypeOK /\ Inv3_R4_0_I1 /\ Inv1902_R0_1_I2 /\ Next => Inv1902_R0_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1902_R0_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv1902_R0_1_I2 /\ RequestVoteAction => Inv1902_R0_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1902_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1902_R0_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv1902_R0_1_I2 /\ UpdateTermAction => Inv1902_R0_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1902_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1902_R0_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_R4_0_I1 /\ Inv1902_R0_1_I2 /\ BecomeLeaderAction => Inv1902_R0_1_I2' BY DEF TypeOK,Inv3_R4_0_I1,BecomeLeaderAction,BecomeLeader,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv1902_R0_1_I2 /\ ClientRequestAction => Inv1902_R0_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1902_R0_1_I2 /\ AdvanceCommitIndexAction => Inv1902_R0_1_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1902_R0_1_I2 /\ AppendEntriesAction => Inv1902_R0_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1902_R0_1_I2 /\ HandleRequestVoteRequestAction => Inv1902_R0_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1902_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1902_R0_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1902_R0_1_I2 /\ HandleRequestVoteResponseAction => Inv1902_R0_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1902_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1902_R0_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1902_R0_1_I2 /\ RejectAppendEntriesRequestAction => Inv1902_R0_1_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1902_R0_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv1902_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1902_R0_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1902_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1902_R0_1_I2
  \* (Inv1902_R0_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1902_R0_1_I2 /\ HandleAppendEntriesResponseAction => Inv1902_R0_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1902_R0_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3_R4_0_I1
THEOREM L_10 == TypeOK /\ Inv3_R4_0_I1 /\ Next => Inv3_R4_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_R4_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_R4_0_I1 /\ RequestVoteAction => Inv3_R4_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_R4_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R4_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_R4_0_I1 /\ UpdateTermAction => Inv3_R4_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_R4_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R4_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_R4_0_I1 /\ BecomeLeaderAction => Inv3_R4_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_R4_0_I1 /\ ClientRequestAction => Inv3_R4_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv3_R4_0_I1 /\ AdvanceCommitIndexAction => Inv3_R4_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv3_R4_0_I1 /\ AppendEntriesAction => Inv3_R4_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv3_R4_0_I1 /\ HandleRequestVoteRequestAction => Inv3_R4_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R4_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R4_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R4_0_I1 /\ HandleRequestVoteResponseAction => Inv3_R4_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R4_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R4_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv3_R4_0_I1 /\ RejectAppendEntriesRequestAction => Inv3_R4_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv3_R4_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv3_R4_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv3_R4_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv3_R4_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv3_R4_0_I1
  \* (Inv3_R4_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv3_R4_0_I1 /\ HandleAppendEntriesResponseAction => Inv3_R4_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_R4_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv12044_R0_1_I2
THEOREM L_11 == TypeOK /\ Inv12044_R0_1_I2 /\ Next => Inv12044_R0_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  <1> USE StaticQuorumsOverlap, FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum, EmptyIntersectionImpliesNotBothQuorums
  \* (Inv12044_R0_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv12044_R0_1_I2 /\ RequestVoteAction => Inv12044_R0_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12044_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12044_R0_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv12044_R0_1_I2 /\ UpdateTermAction => Inv12044_R0_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12044_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12044_R0_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12044_R0_1_I2 /\ BecomeLeaderAction => Inv12044_R0_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv12044_R0_1_I2 /\ ClientRequestAction => Inv12044_R0_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv12044_R0_1_I2 /\ AdvanceCommitIndexAction => Inv12044_R0_1_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv12044_R0_1_I2 /\ AppendEntriesAction => Inv12044_R0_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv12044_R0_1_I2 /\ HandleRequestVoteRequestAction => Inv12044_R0_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12044_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12044_R0_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv12044_R0_1_I2 /\ HandleRequestVoteResponseAction => Inv12044_R0_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv12044_R0_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  (((state[VARI] = Follower)) \/ ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))))'
      BY DEF HandleRequestVoteResponseAction, Inv12044_R0_1_I2
    <2> QED
      BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12044_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12044_R0_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv12044_R0_1_I2 /\ RejectAppendEntriesRequestAction => Inv12044_R0_1_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv12044_R0_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv12044_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv12044_R0_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv12044_R0_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv12044_R0_1_I2
  \* (Inv12044_R0_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv12044_R0_1_I2 /\ HandleAppendEntriesResponseAction => Inv12044_R0_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12044_R0_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
    <1>2. Init => Inv30_R0_0_I0 BY DEF Init, Inv30_R0_0_I0, IndGlobal
    <1>3. Init => Inv15_R0_1_I2 BY DEF Init, Inv15_R0_1_I2, IndGlobal
    <1>4. Init => Inv9_R2_0_I0 BY DEF Init, Inv9_R2_0_I0, IndGlobal
    <1>5. Init => Inv4_R7_0_I0 BY DEF Init, Inv4_R7_0_I0, IndGlobal
    <1>6. Init => Inv17_R0_1_I2 BY DEF Init, Inv17_R0_1_I2, IndGlobal
    <1>7. Init => Inv10_R1_1_I1 BY DEF Init, Inv10_R1_1_I1, IndGlobal
    <1>8. Init => Inv3_R2_1_I0 BY DEF Init, Inv3_R2_1_I0, IndGlobal
    <1>9. Init => Inv1902_R0_1_I2 BY DEF Init, Inv1902_R0_1_I2, IndGlobal
    <1>10. Init => Inv3_R4_0_I1 BY DEF Init, Inv3_R4_0_I1, IndGlobal
    <1>11. Init => Inv12044_R0_1_I2 BY DEF Init, Inv12044_R0_1_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11 DEF Next, IndGlobal


====