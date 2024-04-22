--------------------------------- MODULE AsyncRaft_IndProofs ---------------------------------
EXTENDS AsyncRaft,TLAPS, SequenceTheorems, FunctionTheorems, FiniteSetTheorems, FiniteSets
  
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
\* seed: 1
\* num proof graph nodes: 11
\* num proof obligations: 132
Safety == H_OnePrimaryPerTerm
\*Inv17456_R0_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))) \/ (~(votesGranted[VARJ] \in Quorum))
Inv17456_R0_0_I2 == \A VARI \in Server : \A VARJ \in Server : ( (((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))) /\ ((votesGranted[VARJ] \in Quorum)) ) => ((state[VARJ] = Follower))
Inv6127_R1_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \cap votesGranted[VARJ] = {}) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))
Inv341_R1_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((VARI \in votesGranted[VARI]))
Inv1692_R1_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv100_R2_0_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv10_R2_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv340_R5_0_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] = VARI))
Inv749_R5_0_I1 == \A VARI \in Server : \A VARJ \in Server : (VARI \in votesGranted[VARI]) \/ (~(votedFor[VARJ] = VARI))
Inv4_R5_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv6_R8_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : (VARI \in votesGranted[VARI]) \/ (~(VARREQVM.msource = VARI))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv17456_R0_0_I2
  /\ Inv6127_R1_0_I2
  /\ Inv100_R2_0_I1
  /\ Inv340_R5_0_I1
  /\ Inv749_R5_0_I1
  /\ Inv6_R8_0_I1
  /\ Inv341_R1_1_I1
  /\ Inv4_R5_2_I0
  /\ Inv10_R2_1_I1
  /\ Inv1692_R1_1_I1


\* mean in-degree: 1.1818181818181819
\* median in-degree: 1
\* max in-degree: 4
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
\* /\ Server = {1,2,3} /\ MaxTerm = 3 /\ MaxLogLen = 2 /\ Quorum = {{1,2},{2,3}}

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RequestVoteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,LastTerm
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
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK,Agree,Max
  \* (TypeOK,AppendEntriesAction)
  <1>6. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      <3> SUFFICES ASSUME NEW m \in requestVoteRequestMsgs,
                          HandleRequestVoteRequest(m)
                   PROVE  (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
        BY DEF HandleRequestVoteRequestAction
      <3> QED
        BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
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
  <1>8. TypeOK /\ TypeOK /\ HandleRequestVoteResponseAction => TypeOK'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (TypeOK,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ TypeOK /\ RejectAppendEntriesRequestAction => TypeOK'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,TypeOK,LogOk,AppendEntriesRequestType
  \* (TypeOK,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestAppendAction => TypeOK'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK,AppendEntriesResponseType
  \* (TypeOK,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ TypeOK /\ AcceptAppendEntriesRequestLearnCommitAction => TypeOK'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,TypeOK,AppendEntriesRequestType
  \* (TypeOK,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK,AppendEntriesResponseType,Max
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv17456_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv17456_R0_0_I2 /\ Safety /\ BecomeLeaderAction => Safety'
       BY DEF TypeOK,Inv17456_R0_0_I2,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
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


\*** Inv17456_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv100_R2_0_I1 /\ Inv4_R5_2_I0 /\ Inv6127_R1_0_I2 /\ Inv341_R1_1_I1 /\ Inv6127_R1_0_I2 /\ Inv1692_R1_1_I1 /\ Inv17456_R0_0_I2 /\ Next => Inv17456_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv17456_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv17456_R0_0_I2 /\ RequestVoteAction => Inv17456_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv17456_R0_0_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  ( ( (((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))) /\ ((votesGranted[VARJ] \in Quorum)) ) => 
                            ((state[VARJ] = Follower)))'
      BY DEF Inv17456_R0_0_I2, RequestVoteAction
    <2> QED
      BY FS_Singleton
      DEF TypeOK,RequestVoteAction,RequestVote,Inv17456_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType, LastTerm
       
  \* (Inv17456_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv17456_R0_0_I2 /\ UpdateTermAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv17456_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17456_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6127_R1_0_I2 /\ Inv17456_R0_0_I2 /\ BecomeLeaderAction => Inv17456_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6127_R1_0_I2,
                        Inv17456_R0_0_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        ((((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))) /\ ((votesGranted[VARJ] \in Quorum)))'
                 PROVE  (state[VARJ] = Follower)'
      BY DEF BecomeLeaderAction, Inv17456_R0_0_I2
   <2> QED
      BY StaticQuorumsOverlap DEF TypeOK, BecomeLeaderAction, BecomeLeader, Inv6127_R1_0_I2, Inv17456_R0_0_I2       
  \* (Inv17456_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv17456_R0_0_I2 /\ ClientRequestAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv17456_R0_0_I2
  \* (Inv17456_R0_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv17456_R0_0_I2 /\ AdvanceCommitIndexAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv17456_R0_0_I2
  \* (Inv17456_R0_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv17456_R0_0_I2 /\ AppendEntriesAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv17456_R0_0_I2
  \* (Inv17456_R0_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv17456_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17456_R0_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv100_R2_0_I1 /\ Inv4_R5_2_I0 /\ Inv341_R1_1_I1 /\ Inv6127_R1_0_I2 /\ Inv1692_R1_1_I1 /\ Inv17456_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv17456_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv341_R1_1_I1,
                        Inv6127_R1_0_I2,
                        Inv1692_R1_1_I1,
                        Inv17456_R0_0_I2,
                        Inv4_R5_2_I0,
                        Inv100_R2_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (( (((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))) /\ ((votesGranted[VARJ] \in Quorum)) ) => ((state[VARJ] = Follower)))'
      BY DEF HandleRequestVoteResponseAction, Inv17456_R0_0_I2
    <2>1. CASE m.   mvoteGranted
          <3> USE DEF TypeOK,Inv4_R5_2_I0,Inv100_R2_0_I1,Inv341_R1_1_I1,Inv6127_R1_0_I2,Inv1692_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero  
          <3>1. votesGranted[m.mdest]' = votesGranted[m.mdest] \cup {m.msource} BY <2>1
                      DEF TypeOK,Inv341_R1_1_I1,Inv6127_R1_0_I2,Inv1692_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero              
          <3>4. CASE votesGranted'[VARJ] \notin Quorum BY <3>4 DEF TypeOK
          <3>5. CASE votesGranted'[VARJ] \in Quorum /\ votesGranted[VARJ] \in Quorum
            <4>1 m.msource \in votesGranted'[m.mdest] BY <2>1,<3>5 DEF TypeOK
            <4>2. QED BY FS_Singleton, FS_Union, <2>1, <4>1, <3>5
          <3>6. CASE votesGranted'[VARJ] \in Quorum /\ votesGranted[VARJ] \notin Quorum
            <4>1. CASE VARJ = m.mdest /\ state[VARJ] = Candidate /\ state[VARI] = Leader
\*             BY StaticQuorumsOverlap, FS_Singleton, FS_Union, <2>1, <4>1, <3>6
                <5>1. votesGranted[VARI] \in Quorum BY <4>1
                <5>2. votesGranted'[VARJ] \in Quorum BY <4>1, <3>6
                <5>3. (votesGranted'[VARJ] \cap votesGranted[VARI]) # {} BY StaticQuorumsOverlap, <4>1, <3>6
                <5>8. QED BY <5>1, <5>2, <5>3
            <4>2. CASE VARJ = m.mdest /\ state[VARJ] = Candidate /\ state[VARI] # Leader BY StaticQuorumsOverlap, FS_Singleton, FS_Union, <2>1, <4>1, <3>6
            <4>3. CASE VARJ = m.mdest /\ state[VARJ] = Follower BY  FS_Singleton, FS_Union, StaticQuorumsOverlap, AddingToQuorumRemainsQuorum, <2>1, <4>3, <3>6
            <4>4. CASE VARJ # m.mdest BY FS_Singleton, FS_Union, <2>1, <4>4, <3>6
            <4>5. QED BY <4>1, <4>2, <4>3, <4>4
          <3>10. QED BY <2>1,<3>1,<3>4,<3>5,<3>6,FS_Singleton, FS_Difference, FS_Subset, FS_Union, FS_Intersection, StaticQuorumsOverlap, AddingToQuorumRemainsQuorum 
            DEF TypeOK,Inv341_R1_1_I1,Inv6127_R1_0_I2,Inv1692_R1_1_I1,HandleRequestVoteResponseAction,
                HandleRequestVoteResponse,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero              
\*      DEF TypeOK,Inv341_R1_1_I1,Inv6127_R1_0_I2,Inv1692_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE ~(m.mvoteGranted)
          <3>1. QED BY <2>2,FS_Singleton, FS_Difference, FS_Subset, FS_Union, FS_Intersection, StaticQuorumsOverlap, AddingToQuorumRemainsQuorum 
            DEF TypeOK,Inv341_R1_1_I1,Inv6127_R1_0_I2,Inv1692_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero 
    <2> QED
      BY <2>1, <2>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, FS_Intersection, StaticQuorumsOverlap, AddingToQuorumRemainsQuorum 
      DEF TypeOK,Inv341_R1_1_I1,Inv6127_R1_0_I2,Inv1692_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17456_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv17456_R0_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv17456_R0_0_I2 /\ RejectAppendEntriesRequestAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv17456_R0_0_I2
  \* (Inv17456_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv17456_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv17456_R0_0_I2
  \* (Inv17456_R0_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv17456_R0_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv17456_R0_0_I2
  \* (Inv17456_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv17456_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv17456_R0_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv17456_R0_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6127_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv10_R2_1_I1 /\ Inv100_R2_0_I1 /\ Inv6127_R1_0_I2 /\ Next => Inv6127_R1_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6127_R1_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_1_I1 /\ Inv6127_R1_0_I2 /\ RequestVoteAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,Inv10_R2_1_I1,RequestVoteAction,RequestVote,Inv6127_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6127_R1_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6127_R1_0_I2 /\ UpdateTermAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6127_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6127_R1_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6127_R1_0_I2 /\ BecomeLeaderAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6127_R1_0_I2 /\ ClientRequestAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6127_R1_0_I2 /\ AdvanceCommitIndexAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6127_R1_0_I2 /\ AppendEntriesAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6127_R1_0_I2 /\ HandleRequestVoteRequestAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6127_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6127_R1_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv100_R2_0_I1 /\ Inv6127_R1_0_I2 /\ HandleRequestVoteResponseAction => Inv6127_R1_0_I2'
       BY FS_Singleton DEF TypeOK,Inv100_R2_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6127_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6127_R1_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6127_R1_0_I2 /\ RejectAppendEntriesRequestAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6127_R1_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6127_R1_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6127_R1_0_I2
  \* (Inv6127_R1_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6127_R1_0_I2 /\ HandleAppendEntriesResponseAction => Inv6127_R1_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6127_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv100_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv4_R5_2_I0 /\ Inv340_R5_0_I1 /\ Inv749_R5_0_I1 /\ Inv341_R1_1_I1 /\ Inv100_R2_0_I1 /\ Next => Inv100_R2_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv100_R2_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv4_R5_2_I0 /\ Inv100_R2_0_I1 /\ RequestVoteAction => Inv100_R2_0_I1'
       BY DEF TypeOK,Inv4_R5_2_I0,RequestVoteAction,RequestVote,Inv100_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv100_R2_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv100_R2_0_I1 /\ UpdateTermAction => Inv100_R2_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv100_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv100_R2_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv100_R2_0_I1 /\ BecomeLeaderAction => Inv100_R2_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv100_R2_0_I1 /\ ClientRequestAction => Inv100_R2_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv100_R2_0_I1 /\ AdvanceCommitIndexAction => Inv100_R2_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv100_R2_0_I1 /\ AppendEntriesAction => Inv100_R2_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv340_R5_0_I1 /\ Inv749_R5_0_I1 /\ Inv100_R2_0_I1 /\ Inv4_R5_2_I0 /\ HandleRequestVoteRequestAction => Inv100_R2_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv340_R5_0_I1,
                        Inv749_R5_0_I1,
                        Inv100_R2_0_I1,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))'
      BY DEF HandleRequestVoteRequestAction, Inv100_R2_0_I1
    <2> QED
      BY FS_Singleton, FS_Subset, FS_Union DEF TypeOK,Inv340_R5_0_I1,Inv4_R5_2_I0,Inv749_R5_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv100_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv100_R2_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv341_R1_1_I1 /\ Inv100_R2_0_I1 /\ Inv4_R5_2_I0 /\ HandleRequestVoteResponseAction => Inv100_R2_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv341_R1_1_I1,
                        Inv100_R2_0_I1,
                        Inv4_R5_2_I0,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))'
      BY DEF HandleRequestVoteResponseAction, Inv100_R2_0_I1,Inv4_R5_2_I0, Inv341_R1_1_I1,Inv100_R2_0_I1
    <2> QED
      BY StaticQuorumsOverlap, FS_Singleton, FS_Union, FS_Difference, FS_Subset DEF TypeOK,Inv341_R1_1_I1,Inv4_R5_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv100_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv100_R2_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv100_R2_0_I1 /\ RejectAppendEntriesRequestAction => Inv100_R2_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv100_R2_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv100_R2_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv100_R2_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv100_R2_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv100_R2_0_I1
  \* (Inv100_R2_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv100_R2_0_I1 /\ HandleAppendEntriesResponseAction => Inv100_R2_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv100_R2_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv340_R5_0_I1
THEOREM L_5 == TypeOK /\ Inv340_R5_0_I1 /\ Next => Inv340_R5_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv340_R5_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv340_R5_0_I1 /\ RequestVoteAction => Inv340_R5_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv340_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv340_R5_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv340_R5_0_I1 /\ UpdateTermAction => Inv340_R5_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv340_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv340_R5_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv340_R5_0_I1 /\ BecomeLeaderAction => Inv340_R5_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv340_R5_0_I1 /\ ClientRequestAction => Inv340_R5_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv340_R5_0_I1 /\ AdvanceCommitIndexAction => Inv340_R5_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv340_R5_0_I1 /\ AppendEntriesAction => Inv340_R5_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv340_R5_0_I1 /\ HandleRequestVoteRequestAction => Inv340_R5_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv340_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv340_R5_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv340_R5_0_I1 /\ HandleRequestVoteResponseAction => Inv340_R5_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv340_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv340_R5_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv340_R5_0_I1 /\ RejectAppendEntriesRequestAction => Inv340_R5_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv340_R5_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv340_R5_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv340_R5_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv340_R5_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv340_R5_0_I1
  \* (Inv340_R5_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv340_R5_0_I1 /\ HandleAppendEntriesResponseAction => Inv340_R5_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv340_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv749_R5_0_I1
THEOREM L_6 == TypeOK /\ Inv6_R8_0_I1 /\ Inv749_R5_0_I1 /\ Next => Inv749_R5_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv749_R5_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv749_R5_0_I1 /\ RequestVoteAction => Inv749_R5_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv749_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv749_R5_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv749_R5_0_I1 /\ UpdateTermAction => Inv749_R5_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv749_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv749_R5_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv749_R5_0_I1 /\ BecomeLeaderAction => Inv749_R5_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv749_R5_0_I1 /\ ClientRequestAction => Inv749_R5_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv749_R5_0_I1 /\ AdvanceCommitIndexAction => Inv749_R5_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv749_R5_0_I1 /\ AppendEntriesAction => Inv749_R5_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R8_0_I1 /\ Inv749_R5_0_I1 /\ HandleRequestVoteRequestAction => Inv749_R5_0_I1'
       BY DEF TypeOK,Inv6_R8_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv749_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv749_R5_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv749_R5_0_I1 /\ HandleRequestVoteResponseAction => Inv749_R5_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv749_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv749_R5_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv749_R5_0_I1 /\ RejectAppendEntriesRequestAction => Inv749_R5_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv749_R5_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv749_R5_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv749_R5_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv749_R5_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv749_R5_0_I1
  \* (Inv749_R5_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv749_R5_0_I1 /\ HandleAppendEntriesResponseAction => Inv749_R5_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv749_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6_R8_0_I1
THEOREM L_7 == TypeOK /\ Inv6_R8_0_I1 /\ Next => Inv6_R8_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_R8_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R8_0_I1 /\ RequestVoteAction => Inv6_R8_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_R8_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R8_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R8_0_I1 /\ UpdateTermAction => Inv6_R8_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_R8_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R8_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_R8_0_I1 /\ BecomeLeaderAction => Inv6_R8_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_R8_0_I1 /\ ClientRequestAction => Inv6_R8_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6_R8_0_I1 /\ AdvanceCommitIndexAction => Inv6_R8_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6_R8_0_I1 /\ AppendEntriesAction => Inv6_R8_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R8_0_I1 /\ HandleRequestVoteRequestAction => Inv6_R8_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_R8_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R8_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R8_0_I1 /\ HandleRequestVoteResponseAction => Inv6_R8_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_R8_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R8_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6_R8_0_I1 /\ RejectAppendEntriesRequestAction => Inv6_R8_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6_R8_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv6_R8_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6_R8_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6_R8_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6_R8_0_I1
  \* (Inv6_R8_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6_R8_0_I1 /\ HandleAppendEntriesResponseAction => Inv6_R8_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_R8_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv341_R1_1_I1
THEOREM L_8 == TypeOK /\ Inv341_R1_1_I1 /\ Next => Inv341_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv341_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv341_R1_1_I1 /\ RequestVoteAction => Inv341_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv341_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv341_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv341_R1_1_I1 /\ UpdateTermAction => Inv341_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv341_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv341_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv341_R1_1_I1 /\ BecomeLeaderAction => Inv341_R1_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv341_R1_1_I1 /\ ClientRequestAction => Inv341_R1_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv341_R1_1_I1 /\ AdvanceCommitIndexAction => Inv341_R1_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv341_R1_1_I1 /\ AppendEntriesAction => Inv341_R1_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv341_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv341_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv341_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv341_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv341_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv341_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv341_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv341_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv341_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv341_R1_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv341_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv341_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv341_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv341_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv341_R1_1_I1
  \* (Inv341_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv341_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv341_R1_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv341_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv4_R5_2_I0
THEOREM L_9 == TypeOK /\ Inv4_R5_2_I0 /\ Next => Inv4_R5_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4_R5_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv4_R5_2_I0 /\ RequestVoteAction => Inv4_R5_2_I0'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv4_R5_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_R5_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv4_R5_2_I0 /\ UpdateTermAction => Inv4_R5_2_I0'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_R5_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_R5_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_R5_2_I0 /\ BecomeLeaderAction => Inv4_R5_2_I0'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv4_R5_2_I0 /\ ClientRequestAction => Inv4_R5_2_I0'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv4_R5_2_I0 /\ AdvanceCommitIndexAction => Inv4_R5_2_I0'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv4_R5_2_I0 /\ AppendEntriesAction => Inv4_R5_2_I0'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv4_R5_2_I0 /\ HandleRequestVoteRequestAction => Inv4_R5_2_I0'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_R5_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_R5_2_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv4_R5_2_I0 /\ HandleRequestVoteResponseAction => Inv4_R5_2_I0'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_R5_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_R5_2_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv4_R5_2_I0 /\ RejectAppendEntriesRequestAction => Inv4_R5_2_I0'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv4_R5_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv4_R5_2_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv4_R5_2_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv4_R5_2_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv4_R5_2_I0
  \* (Inv4_R5_2_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv4_R5_2_I0 /\ HandleAppendEntriesResponseAction => Inv4_R5_2_I0'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_R5_2_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R2_1_I1
THEOREM L_10 == TypeOK /\ Inv4_R5_2_I0 /\ Inv10_R2_1_I1 /\ Next => Inv10_R2_1_I1'
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
  <1>8. TypeOK /\ Inv4_R5_2_I0 /\ Inv10_R2_1_I1 /\ HandleRequestVoteResponseAction => Inv10_R2_1_I1'
       BY DEF TypeOK,Inv4_R5_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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


\*** Inv1692_R1_1_I1
THEOREM L_11 == TypeOK /\ Inv1692_R1_1_I1 /\ Next => Inv1692_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1692_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1692_R1_1_I1 /\ RequestVoteAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1692_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1692_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1692_R1_1_I1 /\ UpdateTermAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1692_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1692_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1692_R1_1_I1 /\ BecomeLeaderAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1692_R1_1_I1 /\ ClientRequestAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1692_R1_1_I1 /\ AdvanceCommitIndexAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1692_R1_1_I1 /\ AppendEntriesAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1692_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1692_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1692_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1692_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv1692_R1_1_I1'
    <2> SUFFICES ASSUME TypeOK,
                       Inv1692_R1_1_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  ((votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader))))'
      BY DEF HandleRequestVoteResponseAction, Inv1692_R1_1_I1
    <2> USE DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1692_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>1. CASE m.mvoteGranted
        <3>1. CASE VARI = m.mdest BY AddingToQuorumRemainsQuorum,FS_Singleton, <2>1 DEF TypeOK
        <3>2. CASE VARI # m.mdest 
            <4>1. votesGranted[VARI] = votesGranted'[VARI] BY <3>2
            <4>2. QED BY <4>1
        <3>3. QED BY <3>1, <3>2
    <2>2. CASE ~m.mvoteGranted 
        <3>1. CASE VARI = m.mdest BY <2>2 DEF TypeOK
        <3>2. CASE VARI # m.mdest 
            <4>1. votesGranted[VARI] = votesGranted'[VARI] BY <3>2
            <4>2. QED BY <4>1
        <3>3. QED BY <3>1, <3>2
    <2> QED
      BY <2>1, <2>2, FS_Subset, FS_Difference, FS_Singleton, FS_Union DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1692_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    
       
  \* (Inv1692_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1692_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1692_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1692_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1692_R1_1_I1
  \* (Inv1692_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1692_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv1692_R1_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1692_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
    <1>2. Init => Inv17456_R0_0_I2 BY DEF Init, Inv17456_R0_0_I2, IndGlobal
    <1>3. Init => Inv6127_R1_0_I2 BY DEF Init, Inv6127_R1_0_I2, IndGlobal
    <1>4. Init => Inv100_R2_0_I1 BY DEF Init, Inv100_R2_0_I1, IndGlobal
    <1>5. Init => Inv340_R5_0_I1 BY DEF Init, Inv340_R5_0_I1, IndGlobal
    <1>6. Init => Inv749_R5_0_I1 BY DEF Init, Inv749_R5_0_I1, IndGlobal
    <1>7. Init => Inv6_R8_0_I1 BY DEF Init, Inv6_R8_0_I1, IndGlobal
    <1>8. Init => Inv341_R1_1_I1 BY DEF Init, Inv341_R1_1_I1, IndGlobal
    <1>9. Init => Inv4_R5_2_I0 BY DEF Init, Inv4_R5_2_I0, IndGlobal
    <1>10. Init => Inv10_R2_1_I1 BY DEF Init, Inv10_R2_1_I1, IndGlobal
    <1>11. Init => Inv1692_R1_1_I1 BY DEF Init, Inv1692_R1_1_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11 DEF Next, IndGlobal

====