--------------------------------- MODULE AsyncRaft_IndProofs ---------------------------------
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


 LEMMA StaticQuorumsOverlap ==
 ASSUME NEW cfg \in SUBSET Server,
        NEW Q1 \in Quorum,
        NEW Q2 \in Quorum
 PROVE Q1 \cap Q2 # {}
 PROOF
     <1>. IsFiniteSet(cfg)
         BY FS_Subset, IsFiniteSet(Server)
     <1>. IsFiniteSet(Q1) /\ IsFiniteSet(Q2)
         BY QuorumsAreServerSubsets, IsFiniteSet(Server), FS_Subset DEF Quorum
     <1>. IsFiniteSet(Q1 \cap Q2)
         BY FS_Intersection
     <1>1. Q1 \in SUBSET cfg /\ Q2 \in SUBSET cfg
         BY QuorumsAreServerSubsets DEF Quorum, TypeOK
     <1>2. Cardinality(Q1) + Cardinality(Q2) <= Cardinality(cfg) + Cardinality(Q1 \cap Q2)
         <2>1. Cardinality(Q1 \cup Q2) = Cardinality(Q1) + Cardinality(Q2) - Cardinality(Q1 \cap Q2)
             BY FS_Union
         <2>2. Cardinality(Q1 \cup Q2) <= Cardinality(cfg)
             BY <1>1, FS_Subset, IsFiniteSet(Server)
         <2>3. QED BY <2>1, <2>2, FS_CardinalityType
     <1>3. Cardinality(Q1) + Cardinality(Q2) < Cardinality(Q1) + Cardinality(Q2) + Cardinality(Q1 \cap Q2)
         <2>1. Cardinality(Q1) * 2 > Cardinality(cfg) /\ Cardinality(Q2) * 2 > Cardinality(cfg)
             BY <1>1 DEF Quorum, TypeOK
         <2>2. Cardinality(Q1) + Cardinality(Q2) > Cardinality(cfg)
             BY <2>1, FS_CardinalityType, IsFiniteSet(Server)
         <2>3. QED BY <2>2, <1>2, FS_CardinalityType
     <1>4. Cardinality(Q1 \cap Q2) > 0
         BY <1>3, FS_CardinalityType
     <1>5. QED BY <1>4, FS_EmptySet
     
     

\* Proof Graph Stats
\* ==================
\* seed: 5
\* num proof graph nodes: 17
\* num proof obligations: 204
Safety == H_OnePrimaryPerTerm
Inv18064_R0_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])))
Inv9598_R1_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \cap votesGranted[VARJ] = {})) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])))
Inv319_R1_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((VARI \in votesGranted[VARI]))
Inv1554_R1_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv226_R1_1_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm) \/ (~(VARREQVRES.mvoteGranted))
Inv112_R2_0_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv10_R2_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv214_R6_0_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] = VARI))
Inv300_R6_0_I1 == \A VARI \in Server : (VARI \in votesGranted[VARI]) \/ (~(votesGranted[VARI] \in Quorum))
Inv297_R6_0_I1 == \A VARI \in Server : \A VARJ \in Server : (VARI \in votesGranted[VARI]) \/ (~(votedFor[VARJ] = VARI))
Inv11_R6_0_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~(votedFor[VARI] = VARJ))
Inv7_R6_1_I1 == \A VARI \in Server : \A VARJ \in Server : (VARI \in votesGranted[VARI]) \/ (~(VARJ \in votesGranted[VARI]))
Inv6_R6_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv4_R10_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)
Inv1_R12_0_I1 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : (VARI \in votesGranted[VARI]) \/ (~(VARREQVRES.mdest = VARI))
Inv10_R15_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : (VARI \in votesGranted[VARI]) \/ (~(VARREQVM.msource = VARI))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv18064_R0_0_I2
  /\ Inv9598_R1_0_I2
  /\ Inv112_R2_0_I1
  /\ Inv214_R6_0_I1
  /\ Inv300_R6_0_I1
  /\ Inv7_R6_1_I1
  /\ Inv1_R12_0_I1
  /\ Inv10_R15_0_I1
  /\ Inv297_R6_0_I1
  /\ Inv4_R10_0_I0
  /\ Inv11_R6_0_I1
  /\ Inv10_R2_1_I1
  /\ Inv6_R6_2_I0
  /\ Inv319_R1_1_I1
  /\ Inv1554_R1_1_I1
  /\ Inv226_R1_1_I1


\* mean in-degree: 1.3529411764705883
\* median in-degree: 1
\* max in-degree: 7
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
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK'
       BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,UpdateTermAction)
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
  \* (TypeOK,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ TypeOK /\ AdvanceCommitIndexAction => TypeOK'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>6. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ TypeOK /\ RejectAppendEntriesRequestAction => TypeOK'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,TypeOK
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
  \* (TypeOK,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestLearnCommitAction => TypeOK'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,TypeOK
  \* (TypeOK,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv18064_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv18064_R0_0_I2 /\ Safety /\ BecomeLeaderAction => Safety'
       BY DEF TypeOK,Inv18064_R0_0_I2,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Safety /\ ClientRequestAction => Safety'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Safety /\ AdvanceCommitIndexAction => Safety'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Safety,H_OnePrimaryPerTerm
  \* (Safety,AppendEntriesAction)
  <1>6. TypeOK /\ Safety /\ AppendEntriesAction => Safety'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Safety /\ RejectAppendEntriesRequestAction => Safety'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Safety /\ AcceptAppendEntriesRequestLearnCommitAction => Safety'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv18064_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv9598_R1_0_I2 /\ Inv319_R1_1_I1 /\ Inv9598_R1_0_I2 /\ Inv1554_R1_1_I1 /\ Inv226_R1_1_I1 /\ Inv18064_R0_0_I2 /\ Next => Inv18064_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv18064_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv18064_R0_0_I2 /\ RequestVoteAction => Inv18064_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv18064_R0_0_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF Inv18064_R0_0_I2, RequestVoteAction
    <2> QED
      BY FS_Singleton, AddingToQuorumRemainsQuorum, FS_Union DEF TypeOK,RequestVoteAction,RequestVote,Inv18064_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
       
  \* (Inv18064_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv18064_R0_0_I2 /\ UpdateTermAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv18064_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18064_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9598_R1_0_I2 /\ Inv18064_R0_0_I2 /\ BecomeLeaderAction => Inv18064_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv9598_R1_0_I2,
                        Inv18064_R0_0_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF BecomeLeaderAction, Inv18064_R0_0_I2
    <2> QED
      BY StaticQuorumsOverlap, FS_Union DEF TypeOK,Inv9598_R1_0_I2,BecomeLeaderAction,BecomeLeader,Inv18064_R0_0_I2
       
  \* (Inv18064_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv18064_R0_0_I2 /\ ClientRequestAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv18064_R0_0_I2
  \* (Inv18064_R0_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv18064_R0_0_I2 /\ AdvanceCommitIndexAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv18064_R0_0_I2
  \* (Inv18064_R0_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv18064_R0_0_I2 /\ AppendEntriesAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv18064_R0_0_I2
  \* (Inv18064_R0_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv18064_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv18064_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18064_R0_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv319_R1_1_I1 /\ Inv9598_R1_0_I2 /\ Inv1554_R1_1_I1 /\ Inv226_R1_1_I1 /\ Inv18064_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv18064_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv319_R1_1_I1,
                        Inv9598_R1_0_I2,
                        Inv1554_R1_1_I1,
                        Inv226_R1_1_I1,
                        Inv18064_R0_0_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF HandleRequestVoteResponseAction, Inv18064_R0_0_I2
    <2> QED
      BY StaticQuorumsOverlap,AddingToQuorumRemainsQuorum, FS_Singleton, FS_Union DEF TypeOK,Inv319_R1_1_I1,Inv9598_R1_0_I2,Inv1554_R1_1_I1,Inv226_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv18064_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv18064_R0_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv18064_R0_0_I2 /\ RejectAppendEntriesRequestAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv18064_R0_0_I2
  \* (Inv18064_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv18064_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv18064_R0_0_I2
  \* (Inv18064_R0_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv18064_R0_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv18064_R0_0_I2
  \* (Inv18064_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv18064_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv18064_R0_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv18064_R0_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv9598_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv10_R2_1_I1 /\ Inv112_R2_0_I1 /\ Inv9598_R1_0_I2 /\ Next => Inv9598_R1_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9598_R1_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_1_I1 /\ Inv9598_R1_0_I2 /\ RequestVoteAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,Inv10_R2_1_I1,RequestVoteAction,RequestVote,Inv9598_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9598_R1_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv9598_R1_0_I2 /\ UpdateTermAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9598_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9598_R1_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9598_R1_0_I2 /\ BecomeLeaderAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv9598_R1_0_I2 /\ ClientRequestAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv9598_R1_0_I2 /\ AdvanceCommitIndexAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv9598_R1_0_I2 /\ AppendEntriesAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv9598_R1_0_I2 /\ HandleRequestVoteRequestAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9598_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9598_R1_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv112_R2_0_I1 /\ Inv9598_R1_0_I2 /\ HandleRequestVoteResponseAction => Inv9598_R1_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv112_R2_0_I1,
                        Inv9598_R1_0_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \cap votesGranted[VARJ] = {})) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF HandleRequestVoteResponseAction, Inv9598_R1_0_I2
    <2> QED
      BY DEF TypeOK,Inv112_R2_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9598_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv9598_R1_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv9598_R1_0_I2 /\ RejectAppendEntriesRequestAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv9598_R1_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv9598_R1_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv9598_R1_0_I2
  \* (Inv9598_R1_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv9598_R1_0_I2 /\ HandleAppendEntriesResponseAction => Inv9598_R1_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9598_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv112_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv6_R6_2_I0 /\ Inv214_R6_0_I1 /\ Inv300_R6_0_I1 /\ Inv297_R6_0_I1 /\ Inv11_R6_0_I1 /\ Inv7_R6_1_I1 /\ Inv10_R2_1_I1 /\ Inv112_R2_0_I1 /\ Next => Inv112_R2_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv112_R2_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R6_2_I0 /\ Inv112_R2_0_I1 /\ RequestVoteAction => Inv112_R2_0_I1'
       BY DEF TypeOK,Inv6_R6_2_I0,RequestVoteAction,RequestVote,Inv112_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv112_R2_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv112_R2_0_I1 /\ UpdateTermAction => Inv112_R2_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv112_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv112_R2_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv112_R2_0_I1 /\ BecomeLeaderAction => Inv112_R2_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv112_R2_0_I1 /\ ClientRequestAction => Inv112_R2_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv112_R2_0_I1 /\ AdvanceCommitIndexAction => Inv112_R2_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv112_R2_0_I1 /\ AppendEntriesAction => Inv112_R2_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv214_R6_0_I1 /\ Inv300_R6_0_I1 /\ Inv297_R6_0_I1 /\ Inv11_R6_0_I1 /\ Inv112_R2_0_I1 /\ HandleRequestVoteRequestAction => Inv112_R2_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv214_R6_0_I1,
                        Inv300_R6_0_I1,
                        Inv297_R6_0_I1,
                        Inv11_R6_0_I1,
                        Inv112_R2_0_I1,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))'
      BY DEF HandleRequestVoteRequestAction, Inv112_R2_0_I1
    <2> QED
      BY DEF TypeOK,Inv214_R6_0_I1,Inv300_R6_0_I1,Inv297_R6_0_I1,Inv11_R6_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv112_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv112_R2_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv7_R6_1_I1 /\ Inv10_R2_1_I1 /\ Inv112_R2_0_I1 /\ HandleRequestVoteResponseAction => Inv112_R2_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv7_R6_1_I1,
                        Inv10_R2_1_I1,
                        Inv112_R2_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))'
      BY DEF HandleRequestVoteResponseAction, Inv112_R2_0_I1
    <2> QED
      BY StaticQuorumsOverlap, FS_Singleton, AddingToQuorumRemainsQuorum, FS_Union DEF TypeOK,Inv7_R6_1_I1,Inv10_R2_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv112_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv112_R2_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv112_R2_0_I1 /\ RejectAppendEntriesRequestAction => Inv112_R2_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv112_R2_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv112_R2_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv112_R2_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv112_R2_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv112_R2_0_I1
  \* (Inv112_R2_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv112_R2_0_I1 /\ HandleAppendEntriesResponseAction => Inv112_R2_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv112_R2_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv214_R6_0_I1
THEOREM L_5 == TypeOK /\ Inv214_R6_0_I1 /\ Next => Inv214_R6_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv214_R6_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv214_R6_0_I1 /\ RequestVoteAction => Inv214_R6_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv214_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv214_R6_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv214_R6_0_I1 /\ UpdateTermAction => Inv214_R6_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv214_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv214_R6_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv214_R6_0_I1 /\ BecomeLeaderAction => Inv214_R6_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv214_R6_0_I1 /\ ClientRequestAction => Inv214_R6_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv214_R6_0_I1 /\ AdvanceCommitIndexAction => Inv214_R6_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv214_R6_0_I1 /\ AppendEntriesAction => Inv214_R6_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv214_R6_0_I1 /\ HandleRequestVoteRequestAction => Inv214_R6_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv214_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv214_R6_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv214_R6_0_I1 /\ HandleRequestVoteResponseAction => Inv214_R6_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv214_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv214_R6_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv214_R6_0_I1 /\ RejectAppendEntriesRequestAction => Inv214_R6_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv214_R6_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv214_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv214_R6_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv214_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv214_R6_0_I1
  \* (Inv214_R6_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv214_R6_0_I1 /\ HandleAppendEntriesResponseAction => Inv214_R6_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv214_R6_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv300_R6_0_I1
THEOREM L_6 == TypeOK /\ Inv7_R6_1_I1 /\ Inv300_R6_0_I1 /\ Next => Inv300_R6_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv300_R6_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv300_R6_0_I1 /\ RequestVoteAction => Inv300_R6_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv300_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv300_R6_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv300_R6_0_I1 /\ UpdateTermAction => Inv300_R6_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv300_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv300_R6_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv300_R6_0_I1 /\ BecomeLeaderAction => Inv300_R6_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv300_R6_0_I1 /\ ClientRequestAction => Inv300_R6_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv300_R6_0_I1 /\ AdvanceCommitIndexAction => Inv300_R6_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv300_R6_0_I1 /\ AppendEntriesAction => Inv300_R6_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv300_R6_0_I1 /\ HandleRequestVoteRequestAction => Inv300_R6_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv300_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv300_R6_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv7_R6_1_I1 /\ Inv300_R6_0_I1 /\ HandleRequestVoteResponseAction => Inv300_R6_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv7_R6_1_I1,
                        Inv300_R6_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((VARI \in votesGranted[VARI]) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF HandleRequestVoteResponseAction, Inv300_R6_0_I1
    <2> QED
      BY StaticQuorumsOverlap, FS_Singleton, AddingToQuorumRemainsQuorum DEF TypeOK,Inv7_R6_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv300_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv300_R6_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv300_R6_0_I1 /\ RejectAppendEntriesRequestAction => Inv300_R6_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv300_R6_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv300_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv300_R6_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv300_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv300_R6_0_I1
  \* (Inv300_R6_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv300_R6_0_I1 /\ HandleAppendEntriesResponseAction => Inv300_R6_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv300_R6_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv7_R6_1_I1
THEOREM L_7 == TypeOK /\ Inv1_R12_0_I1 /\ Inv7_R6_1_I1 /\ Next => Inv7_R6_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_R6_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_R6_1_I1 /\ RequestVoteAction => Inv7_R6_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_R6_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_R6_1_I1 /\ UpdateTermAction => Inv7_R6_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_R6_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_R6_1_I1 /\ BecomeLeaderAction => Inv7_R6_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_R6_1_I1 /\ ClientRequestAction => Inv7_R6_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv7_R6_1_I1 /\ AdvanceCommitIndexAction => Inv7_R6_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv7_R6_1_I1 /\ AppendEntriesAction => Inv7_R6_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv7_R6_1_I1 /\ HandleRequestVoteRequestAction => Inv7_R6_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_R6_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R12_0_I1 /\ Inv7_R6_1_I1 /\ HandleRequestVoteResponseAction => Inv7_R6_1_I1'
       BY DEF TypeOK,Inv1_R12_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_R6_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv7_R6_1_I1 /\ RejectAppendEntriesRequestAction => Inv7_R6_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv7_R6_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv7_R6_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv7_R6_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv7_R6_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv7_R6_1_I1
  \* (Inv7_R6_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv7_R6_1_I1 /\ HandleAppendEntriesResponseAction => Inv7_R6_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_R6_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_R12_0_I1
THEOREM L_8 == TypeOK /\ Inv10_R15_0_I1 /\ Inv1_R12_0_I1 /\ Next => Inv1_R12_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1_R12_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1_R12_0_I1 /\ RequestVoteAction => Inv1_R12_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1_R12_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R12_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R12_0_I1 /\ UpdateTermAction => Inv1_R12_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1_R12_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R12_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1_R12_0_I1 /\ BecomeLeaderAction => Inv1_R12_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1_R12_0_I1 /\ ClientRequestAction => Inv1_R12_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1_R12_0_I1 /\ AdvanceCommitIndexAction => Inv1_R12_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1_R12_0_I1 /\ AppendEntriesAction => Inv1_R12_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R15_0_I1 /\ Inv1_R12_0_I1 /\ HandleRequestVoteRequestAction => Inv1_R12_0_I1'
       BY DEF TypeOK,Inv10_R15_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1_R12_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R12_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R12_0_I1 /\ HandleRequestVoteResponseAction => Inv1_R12_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1_R12_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R12_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1_R12_0_I1 /\ RejectAppendEntriesRequestAction => Inv1_R12_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1_R12_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1_R12_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1_R12_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1_R12_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1_R12_0_I1
  \* (Inv1_R12_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1_R12_0_I1 /\ HandleAppendEntriesResponseAction => Inv1_R12_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1_R12_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R15_0_I1
THEOREM L_9 == TypeOK /\ Inv10_R15_0_I1 /\ Next => Inv10_R15_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R15_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R15_0_I1 /\ RequestVoteAction => Inv10_R15_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R15_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R15_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R15_0_I1 /\ UpdateTermAction => Inv10_R15_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R15_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R15_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_R15_0_I1 /\ BecomeLeaderAction => Inv10_R15_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_R15_0_I1 /\ ClientRequestAction => Inv10_R15_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10_R15_0_I1 /\ AdvanceCommitIndexAction => Inv10_R15_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10_R15_0_I1 /\ AppendEntriesAction => Inv10_R15_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R15_0_I1 /\ HandleRequestVoteRequestAction => Inv10_R15_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_R15_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R15_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv10_R15_0_I1 /\ HandleRequestVoteResponseAction => Inv10_R15_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R15_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R15_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R15_0_I1 /\ RejectAppendEntriesRequestAction => Inv10_R15_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R15_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R15_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R15_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R15_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R15_0_I1
  \* (Inv10_R15_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R15_0_I1 /\ HandleAppendEntriesResponseAction => Inv10_R15_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R15_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv297_R6_0_I1
THEOREM L_10 == TypeOK /\ Inv7_R6_1_I1 /\ Inv4_R10_0_I0 /\ Inv11_R6_0_I1 /\ Inv297_R6_0_I1 /\ Next => Inv297_R6_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv297_R6_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv297_R6_0_I1 /\ RequestVoteAction => Inv297_R6_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv297_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv297_R6_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv297_R6_0_I1 /\ UpdateTermAction => Inv297_R6_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv297_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv297_R6_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv297_R6_0_I1 /\ BecomeLeaderAction => Inv297_R6_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv297_R6_0_I1 /\ ClientRequestAction => Inv297_R6_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv297_R6_0_I1 /\ AdvanceCommitIndexAction => Inv297_R6_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv297_R6_0_I1 /\ AppendEntriesAction => Inv297_R6_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv7_R6_1_I1 /\ Inv4_R10_0_I0 /\ Inv11_R6_0_I1 /\ Inv297_R6_0_I1 /\ HandleRequestVoteRequestAction => Inv297_R6_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv7_R6_1_I1,
                        Inv4_R10_0_I0,
                        Inv11_R6_0_I1,
                        Inv297_R6_0_I1,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  ((VARI \in votesGranted[VARI]) \/ (~(votedFor[VARJ] = VARI)))'
      BY DEF HandleRequestVoteRequestAction, Inv297_R6_0_I1
    <2>1. CASE votedFor[m.mdest] = Nil
          BY <2>1, FS_Subset, FS_Doubleton, AddingToQuorumRemainsQuorum, StaticQuorumsOverlap, FS_Union, FS_Singleton, FS_Intersection, FS_Difference 
      DEF TypeOK,Inv7_R6_1_I1,Inv4_R10_0_I0,Inv11_R6_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv297_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
     <2>2. CASE votedFor[m.mdest] = m.msource
          BY <2>2, FS_Subset, FS_Doubleton, AddingToQuorumRemainsQuorum, StaticQuorumsOverlap, FS_Union, FS_Singleton, FS_Intersection, FS_Difference 
      DEF TypeOK,Inv7_R6_1_I1,Inv4_R10_0_I0,Inv11_R6_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv297_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
     <2>3. CASE votedFor[m.mdest] # m.msource /\ votedFor[m.mdest] # Nil
          BY <2>3, FS_Subset, FS_Doubleton, AddingToQuorumRemainsQuorum, StaticQuorumsOverlap, FS_Union, FS_Singleton, FS_Intersection, FS_Difference 
      DEF TypeOK,Inv7_R6_1_I1,Inv4_R10_0_I0,Inv11_R6_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv297_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
               
    <2> QED
      BY <2>1, <2>2, <2>3, FS_Subset, FS_Doubleton, AddingToQuorumRemainsQuorum, StaticQuorumsOverlap, FS_Union, FS_Singleton, FS_Intersection, FS_Difference 
      DEF TypeOK,Inv7_R6_1_I1,Inv4_R10_0_I0,Inv11_R6_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv297_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv297_R6_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv297_R6_0_I1 /\ HandleRequestVoteResponseAction => Inv297_R6_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv297_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv297_R6_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv297_R6_0_I1 /\ RejectAppendEntriesRequestAction => Inv297_R6_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv297_R6_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv297_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv297_R6_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv297_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv297_R6_0_I1
  \* (Inv297_R6_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv297_R6_0_I1 /\ HandleAppendEntriesResponseAction => Inv297_R6_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv297_R6_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4_R10_0_I0
THEOREM L_11 == TypeOK /\ Inv4_R10_0_I0 /\ Next => Inv4_R10_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4_R10_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv4_R10_0_I0 /\ RequestVoteAction => Inv4_R10_0_I0'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_R10_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_R10_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv4_R10_0_I0 /\ UpdateTermAction => Inv4_R10_0_I0'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_R10_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_R10_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_R10_0_I0 /\ BecomeLeaderAction => Inv4_R10_0_I0'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv4_R10_0_I0 /\ ClientRequestAction => Inv4_R10_0_I0'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv4_R10_0_I0 /\ AdvanceCommitIndexAction => Inv4_R10_0_I0'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv4_R10_0_I0 /\ AppendEntriesAction => Inv4_R10_0_I0'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv4_R10_0_I0 /\ HandleRequestVoteRequestAction => Inv4_R10_0_I0'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_R10_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_R10_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv4_R10_0_I0 /\ HandleRequestVoteResponseAction => Inv4_R10_0_I0'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R10_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_R10_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv4_R10_0_I0 /\ RejectAppendEntriesRequestAction => Inv4_R10_0_I0'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv4_R10_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv4_R10_0_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv4_R10_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv4_R10_0_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv4_R10_0_I0
  \* (Inv4_R10_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv4_R10_0_I0 /\ HandleAppendEntriesResponseAction => Inv4_R10_0_I0'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_R10_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv11_R6_0_I1
THEOREM L_12 == TypeOK /\ Inv4_R10_0_I0 /\ Inv11_R6_0_I1 /\ Next => Inv11_R6_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_R6_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv11_R6_0_I1 /\ RequestVoteAction => Inv11_R6_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv11_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_R6_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv11_R6_0_I1 /\ UpdateTermAction => Inv11_R6_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11_R6_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_R6_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_R6_0_I1 /\ BecomeLeaderAction => Inv11_R6_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_R6_0_I1 /\ ClientRequestAction => Inv11_R6_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv11_R6_0_I1 /\ AdvanceCommitIndexAction => Inv11_R6_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv11_R6_0_I1 /\ AppendEntriesAction => Inv11_R6_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv4_R10_0_I0 /\ Inv11_R6_0_I1 /\ HandleRequestVoteRequestAction => Inv11_R6_0_I1'
       BY DEF TypeOK,Inv4_R10_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_R6_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv11_R6_0_I1 /\ HandleRequestVoteResponseAction => Inv11_R6_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_R6_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_R6_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv11_R6_0_I1 /\ RejectAppendEntriesRequestAction => Inv11_R6_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv11_R6_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv11_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv11_R6_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv11_R6_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv11_R6_0_I1
  \* (Inv11_R6_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv11_R6_0_I1 /\ HandleAppendEntriesResponseAction => Inv11_R6_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_R6_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R2_1_I1
THEOREM L_13 == TypeOK /\ Inv6_R6_2_I0 /\ Inv10_R2_1_I1 /\ Next => Inv10_R2_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R2_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_1_I1 /\ RequestVoteAction => Inv10_R2_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R2_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R2_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R2_1_I1 /\ UpdateTermAction => Inv10_R2_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R2_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R2_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_R2_1_I1 /\ BecomeLeaderAction => Inv10_R2_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_R2_1_I1 /\ ClientRequestAction => Inv10_R2_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10_R2_1_I1 /\ AdvanceCommitIndexAction => Inv10_R2_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10_R2_1_I1 /\ AppendEntriesAction => Inv10_R2_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R2_1_I1 /\ HandleRequestVoteRequestAction => Inv10_R2_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R2_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R6_2_I0 /\ Inv10_R2_1_I1 /\ HandleRequestVoteResponseAction => Inv10_R2_1_I1'
       BY DEF TypeOK,Inv6_R6_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R2_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R2_1_I1 /\ RejectAppendEntriesRequestAction => Inv10_R2_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R2_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R2_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R2_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R2_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R2_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_R2_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R2_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6_R6_2_I0
THEOREM L_14 == TypeOK /\ Inv6_R6_2_I0 /\ Next => Inv6_R6_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_R6_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R6_2_I0 /\ RequestVoteAction => Inv6_R6_2_I0'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_R6_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R6_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R6_2_I0 /\ UpdateTermAction => Inv6_R6_2_I0'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_R6_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R6_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_R6_2_I0 /\ BecomeLeaderAction => Inv6_R6_2_I0'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_R6_2_I0 /\ ClientRequestAction => Inv6_R6_2_I0'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6_R6_2_I0 /\ AdvanceCommitIndexAction => Inv6_R6_2_I0'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6_R6_2_I0 /\ AppendEntriesAction => Inv6_R6_2_I0'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R6_2_I0 /\ HandleRequestVoteRequestAction => Inv6_R6_2_I0'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_R6_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R6_2_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R6_2_I0 /\ HandleRequestVoteResponseAction => Inv6_R6_2_I0'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_R6_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R6_2_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6_R6_2_I0 /\ RejectAppendEntriesRequestAction => Inv6_R6_2_I0'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6_R6_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv6_R6_2_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6_R6_2_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6_R6_2_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6_R6_2_I0
  \* (Inv6_R6_2_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6_R6_2_I0 /\ HandleAppendEntriesResponseAction => Inv6_R6_2_I0'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_R6_2_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv319_R1_1_I1
THEOREM L_15 == TypeOK /\ Inv319_R1_1_I1 /\ Next => Inv319_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv319_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv319_R1_1_I1 /\ RequestVoteAction => Inv319_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv319_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv319_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv319_R1_1_I1 /\ UpdateTermAction => Inv319_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv319_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv319_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv319_R1_1_I1 /\ BecomeLeaderAction => Inv319_R1_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv319_R1_1_I1 /\ ClientRequestAction => Inv319_R1_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv319_R1_1_I1 /\ AdvanceCommitIndexAction => Inv319_R1_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv319_R1_1_I1 /\ AppendEntriesAction => Inv319_R1_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv319_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv319_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv319_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv319_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv319_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv319_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv319_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv319_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv319_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv319_R1_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv319_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv319_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv319_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv319_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv319_R1_1_I1
  \* (Inv319_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv319_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv319_R1_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv319_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1554_R1_1_I1
THEOREM L_16 == TypeOK /\ Inv1554_R1_1_I1 /\ Next => Inv1554_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1554_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1554_R1_1_I1 /\ RequestVoteAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1554_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1554_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1554_R1_1_I1 /\ UpdateTermAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1554_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1554_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1554_R1_1_I1 /\ BecomeLeaderAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1554_R1_1_I1 /\ ClientRequestAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1554_R1_1_I1 /\ AdvanceCommitIndexAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1554_R1_1_I1 /\ AppendEntriesAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1554_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1554_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1554_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1554_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv1554_R1_1_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv1554_R1_1_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv1554_R1_1_I1
    <2> QED
      BY StaticQuorumsOverlap, FS_Singleton,AddingToQuorumRemainsQuorum  DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1554_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv1554_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1554_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1554_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1554_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1554_R1_1_I1
  \* (Inv1554_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1554_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv1554_R1_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1554_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv226_R1_1_I1
THEOREM L_17 == TypeOK /\ Inv226_R1_1_I1 /\ Next => Inv226_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv226_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv226_R1_1_I1 /\ RequestVoteAction => Inv226_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv226_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv226_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv226_R1_1_I1 /\ UpdateTermAction => Inv226_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv226_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv226_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv226_R1_1_I1 /\ BecomeLeaderAction => Inv226_R1_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv226_R1_1_I1 /\ ClientRequestAction => Inv226_R1_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv226_R1_1_I1 /\ AdvanceCommitIndexAction => Inv226_R1_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv226_R1_1_I1 /\ AppendEntriesAction => Inv226_R1_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv226_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv226_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv226_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv226_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv226_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv226_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv226_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv226_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv226_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv226_R1_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv226_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv226_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv226_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv226_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv226_R1_1_I1
  \* (Inv226_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv226_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv226_R1_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv226_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
    <1>2. Init => Inv18064_R0_0_I2 BY DEF Init, Inv18064_R0_0_I2, IndGlobal
    <1>3. Init => Inv9598_R1_0_I2 BY DEF Init, Inv9598_R1_0_I2, IndGlobal
    <1>4. Init => Inv112_R2_0_I1 BY DEF Init, Inv112_R2_0_I1, IndGlobal
    <1>5. Init => Inv214_R6_0_I1 BY DEF Init, Inv214_R6_0_I1, IndGlobal
    <1>6. Init => Inv300_R6_0_I1 BY DEF Init, Inv300_R6_0_I1, IndGlobal
    <1>7. Init => Inv7_R6_1_I1 BY DEF Init, Inv7_R6_1_I1, IndGlobal
    <1>8. Init => Inv1_R12_0_I1 BY DEF Init, Inv1_R12_0_I1, IndGlobal
    <1>9. Init => Inv10_R15_0_I1 BY DEF Init, Inv10_R15_0_I1, IndGlobal
    <1>10. Init => Inv297_R6_0_I1 BY DEF Init, Inv297_R6_0_I1, IndGlobal
    <1>11. Init => Inv4_R10_0_I0 BY DEF Init, Inv4_R10_0_I0, IndGlobal
    <1>12. Init => Inv11_R6_0_I1 BY DEF Init, Inv11_R6_0_I1, IndGlobal
    <1>13. Init => Inv10_R2_1_I1 BY DEF Init, Inv10_R2_1_I1, IndGlobal
    <1>14. Init => Inv6_R6_2_I0 BY DEF Init, Inv6_R6_2_I0, IndGlobal
    <1>15. Init => Inv319_R1_1_I1 BY DEF Init, Inv319_R1_1_I1, IndGlobal
    <1>16. Init => Inv1554_R1_1_I1 BY DEF Init, Inv1554_R1_1_I1, IndGlobal
    <1>17. Init => Inv226_R1_1_I1 BY DEF Init, Inv226_R1_1_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17 DEF Next, IndGlobal

====