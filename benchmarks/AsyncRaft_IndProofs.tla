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
\* seed: 4
\* num proof graph nodes: 15
\* num proof obligations: 180
Safety == H_OnePrimaryPerTerm

Inv20249_R0_0_I2 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
        ((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) => 
            (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum)))

Inv10820_R1_0_I2 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
        ((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \cap votesGranted[VARJ] = {})) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])))

Inv25049_R1_1_I2 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
        ~((currentTerm[VARI] >= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~((state[VARJ] \in {Leader,Candidate} /\ VARI # VARJ))))

Inv774_R1_1_I2 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
        (VARI \in votesGranted[VARI]) \/ (~(VARJ \in votesGranted[VARI]))

Inv22_R2_0_I1 == 
    \A VARI \in Server : 
    \A VARJ \in Server : 
    \A VARREQVRES \in requestVoteResponseMsgs : 
        ~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))

Inv10_R2_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv2197_R3_0_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ((currentTerm[VARJ] > currentTerm[VARI])) \/ (((state[VARJ] = Follower))) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv5439_R3_0_I2 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ((state[VARI] = Leader)) \/ (~((state[VARI] = Follower))) \/ ((currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm))
Inv1_R4_0_I1 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : (VARI \in votesGranted[VARI]) \/ (~(VARREQVRES.mdest = VARI))
Inv331_R5_0_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] = VARI))
Inv10_R5_0_I1 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)
Inv7_R5_1_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm) \/ (~(VARREQVRES.mvoteGranted))
Inv6_R5_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv16_R9_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : (VARI \in votesGranted[VARI]) \/ (~(VARREQVM.msource = VARI))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv20249_R0_0_I2
  /\ Inv10820_R1_0_I2
  /\ Inv22_R2_0_I1
  /\ Inv331_R5_0_I1
  /\ Inv774_R1_1_I2
  /\ Inv1_R4_0_I1
  /\ Inv16_R9_0_I1
  /\ Inv10_R5_0_I1
  /\ Inv10_R2_1_I1
  /\ Inv6_R5_2_I0
  /\ Inv7_R5_1_I1
  /\ Inv25049_R1_1_I2
  /\ Inv2197_R3_0_I2
  /\ Inv5439_R3_0_I2


\* mean in-degree: 1.6666666666666667
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

ASSUME Fin == Server = {1,2} /\ Quorum = {{1,2}}

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
  <1>5. TypeOK /\ TypeOK /\ AdvanceCommitIndexAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ AdvanceCommitIndexAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK,Max,Agree
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  \* (TypeOK,AppendEntriesAction)
  <1>6. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ AppendEntriesAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
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
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY FS_Subset DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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
THEOREM L_1 == TypeOK /\ Inv20249_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv20249_R0_0_I2 /\ Safety /\ BecomeLeaderAction => Safety' BY DEF TypeOK,Inv20249_R0_0_I2,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Safety /\ AdvanceCommitIndexAction => Safety' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Safety,H_OnePrimaryPerTerm
  \* (Safety,AppendEntriesAction)
  <1>6. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Safety /\ RejectAppendEntriesRequestAction => Safety' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Safety /\ AcceptAppendEntriesRequestLearnCommitAction => Safety' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv20249_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv10820_R1_0_I2 /\ Inv25049_R1_1_I2 /\ Inv774_R1_1_I2 /\ Inv20249_R0_0_I2 /\ Next => Inv20249_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv20249_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv20249_R0_0_I2 /\ RequestVoteAction => Inv20249_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv20249_R0_0_I2 /\ RequestVoteAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) => (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF Inv20249_R0_0_I2
    <2> QED
      <3> SUFFICES ASSUME (state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])',
                    NEW i \in Server,
                    RequestVote(i)
                   PROVE  (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum)))'
           BY DEF RequestVoteAction
           
      <3>1. CASE VARI = i BY <3>1, FS_Subset, FS_Singleton, AddingToQuorumRemainsQuorum, FS_Singleton, StaticQuorumsOverlap DEF TypeOK,RequestVoteAction,RequestVote,Inv20249_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      <3>2. CASE VARI # i BY <3>2, FS_Subset, FS_Singleton, AddingToQuorumRemainsQuorum, FS_Singleton, StaticQuorumsOverlap DEF TypeOK,RequestVoteAction,RequestVote,Inv20249_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
                
      <3> QED
        BY <3>1, <3>2, FS_Subset, AddingToQuorumRemainsQuorum, FS_Singleton, StaticQuorumsOverlap 
  DEF TypeOK,RequestVoteAction,RequestVote,Inv20249_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
  \* (Inv20249_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv20249_R0_0_I2 /\ UpdateTermAction => Inv20249_R0_0_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv20249_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv20249_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10820_R1_0_I2 /\ Inv20249_R0_0_I2 /\ BecomeLeaderAction => Inv20249_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv10820_R1_0_I2 /\ Inv20249_R0_0_I2 /\ BecomeLeaderAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) => (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF Inv20249_R0_0_I2
    <2> QED
      <3> SUFFICES ASSUME NEW i \in Server,
                          BecomeLeader(i)
                   PROVE  (((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) => (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum))))'
        BY DEF BecomeLeaderAction
      <3> QED
        <4> SUFFICES ASSUME (state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])'
                     PROVE  (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum)))'
          OBVIOUS
        <4> QED
          BY AddingToQuorumRemainsQuorum, FS_Subset, FS_Singleton, FS_Intersection, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv10820_R1_0_I2,BecomeLeaderAction,BecomeLeader,Inv20249_R0_0_I2
        
      
  \* (Inv20249_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv20249_R0_0_I2 /\ ClientRequestAction => Inv20249_R0_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv20249_R0_0_I2
  \* (Inv20249_R0_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv20249_R0_0_I2 /\ AdvanceCommitIndexAction => Inv20249_R0_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv20249_R0_0_I2
  \* (Inv20249_R0_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv20249_R0_0_I2 /\ AppendEntriesAction => Inv20249_R0_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv20249_R0_0_I2
  \* (Inv20249_R0_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv20249_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv20249_R0_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv20249_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv20249_R0_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv25049_R1_1_I2 /\ Inv774_R1_1_I2 /\ Inv20249_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv20249_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv25049_R1_1_I2 /\ Inv774_R1_1_I2 /\ Inv20249_R0_0_I2 /\ HandleRequestVoteResponseAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) => (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF Inv20249_R0_0_I2
    <2> QED
      <3> SUFFICES ASSUME NEW m \in requestVoteResponseMsgs,
                          HandleRequestVoteResponse(m),
                          (state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])'
                   PROVE  (~((state[VARJ] = Leader)) \/ (~(votesGranted[VARI] \in Quorum)))'
        BY DEF HandleRequestVoteResponseAction
      <3>1. CASE VARI = m.mdest BY <3>1, FS_Subset, FS_Singleton, FS_Union, AddingToQuorumRemainsQuorum, FS_Singleton, StaticQuorumsOverlap 
        DEF TypeOK,Inv25049_R1_1_I2,Inv774_R1_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv20249_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      <3>2. CASE VARI # m.mdest BY <3>2, FS_Subset, FS_Singleton, AddingToQuorumRemainsQuorum, FS_Singleton, StaticQuorumsOverlap 
        DEF TypeOK,Inv25049_R1_1_I2,Inv774_R1_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv20249_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
                
      <3> QED
        BY AddingToQuorumRemainsQuorum, FS_Singleton, FS_Subset, FS_Intersection, FS_Union, StaticQuorumsOverlap 
        DEF TypeOK,Inv25049_R1_1_I2,Inv774_R1_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv20249_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
  \* (Inv20249_R0_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv20249_R0_0_I2 /\ RejectAppendEntriesRequestAction => Inv20249_R0_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv20249_R0_0_I2
  \* (Inv20249_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv20249_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv20249_R0_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv20249_R0_0_I2
  \* (Inv20249_R0_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv20249_R0_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv20249_R0_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv20249_R0_0_I2
  \* (Inv20249_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv20249_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv20249_R0_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv20249_R0_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10820_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv10_R2_1_I1 /\ Inv22_R2_0_I1 /\ Inv10820_R1_0_I2 /\ Next => Inv10820_R1_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10820_R1_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_1_I1 /\ Inv10820_R1_0_I2 /\ RequestVoteAction => Inv10820_R1_0_I2' BY DEF TypeOK,Inv10_R2_1_I1,RequestVoteAction,RequestVote,Inv10820_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10820_R1_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv10820_R1_0_I2 /\ UpdateTermAction => Inv10820_R1_0_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10820_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10820_R1_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10820_R1_0_I2 /\ BecomeLeaderAction => Inv10820_R1_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv10820_R1_0_I2 /\ ClientRequestAction => Inv10820_R1_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10820_R1_0_I2 /\ AdvanceCommitIndexAction => Inv10820_R1_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10820_R1_0_I2 /\ AppendEntriesAction => Inv10820_R1_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10820_R1_0_I2 /\ HandleRequestVoteRequestAction => Inv10820_R1_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10820_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10820_R1_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv22_R2_0_I1 /\ Inv10820_R1_0_I2 /\ HandleRequestVoteResponseAction => Inv10820_R1_0_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv22_R2_0_I1 /\ Inv10820_R1_0_I2 /\ HandleRequestVoteResponseAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ ((votesGranted[VARI] \cap votesGranted[VARJ] = {})) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF Inv10820_R1_0_I2
    <2> QED
      BY Fin,FS_Intersection, FS_Singleton, FS_Difference DEF TypeOK,Inv22_R2_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10820_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10820_R1_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10820_R1_0_I2 /\ RejectAppendEntriesRequestAction => Inv10820_R1_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10820_R1_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv10820_R1_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10820_R1_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10820_R1_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10820_R1_0_I2
  \* (Inv10820_R1_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10820_R1_0_I2 /\ HandleAppendEntriesResponseAction => Inv10820_R1_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10820_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv22_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv6_R5_2_I0 /\ Inv331_R5_0_I1 /\ Inv774_R1_1_I2 /\ Inv10_R5_0_I1 /\ Inv774_R1_1_I2 /\ Inv10_R2_1_I1 /\ Inv7_R5_1_I1 /\ Inv22_R2_0_I1 /\ Next => Inv22_R2_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv22_R2_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R5_2_I0 /\ Inv22_R2_0_I1 /\ RequestVoteAction => Inv22_R2_0_I1' BY DEF TypeOK,Inv6_R5_2_I0,RequestVoteAction,RequestVote,Inv22_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22_R2_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv22_R2_0_I1 /\ UpdateTermAction => Inv22_R2_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv22_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv22_R2_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv22_R2_0_I1 /\ BecomeLeaderAction => Inv22_R2_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv22_R2_0_I1 /\ ClientRequestAction => Inv22_R2_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv22_R2_0_I1 /\ AdvanceCommitIndexAction => Inv22_R2_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv22_R2_0_I1 /\ AppendEntriesAction => Inv22_R2_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv331_R5_0_I1 /\ Inv774_R1_1_I2 /\ Inv10_R5_0_I1 /\ Inv22_R2_0_I1 /\ HandleRequestVoteRequestAction => Inv22_R2_0_I1' 
    <2> SUFFICES ASSUME TypeOK /\ Inv331_R5_0_I1 /\ Inv774_R1_1_I2 /\ Inv10_R5_0_I1 /\ Inv22_R2_0_I1 /\ HandleRequestVoteRequestAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))'
      BY DEF Inv22_R2_0_I1
    <2> QED
      BY Fin DEF TypeOK,Inv331_R5_0_I1,Inv774_R1_1_I2,Inv10_R5_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv22_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22_R2_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv774_R1_1_I2 /\ Inv10_R2_1_I1 /\ Inv7_R5_1_I1 /\ Inv22_R2_0_I1 /\ HandleRequestVoteResponseAction => Inv22_R2_0_I1' 
    <2> SUFFICES ASSUME TypeOK /\ Inv774_R1_1_I2 /\ Inv10_R2_1_I1 /\ Inv7_R5_1_I1 /\ Inv22_R2_0_I1 /\ HandleRequestVoteResponseAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted)))'
      BY DEF Inv22_R2_0_I1
    <2> QED
      BY Fin, FS_Singleton, FS_Union DEF TypeOK,Inv774_R1_1_I2,Inv10_R2_1_I1,Inv7_R5_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv22_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv22_R2_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv22_R2_0_I1 /\ RejectAppendEntriesRequestAction => Inv22_R2_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv22_R2_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv22_R2_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv22_R2_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv22_R2_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv22_R2_0_I1
  \* (Inv22_R2_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv22_R2_0_I1 /\ HandleAppendEntriesResponseAction => Inv22_R2_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv22_R2_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv331_R5_0_I1
THEOREM L_5 == TypeOK /\ Inv331_R5_0_I1 /\ Next => Inv331_R5_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv331_R5_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv331_R5_0_I1 /\ RequestVoteAction => Inv331_R5_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv331_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv331_R5_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv331_R5_0_I1 /\ UpdateTermAction => Inv331_R5_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv331_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv331_R5_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv331_R5_0_I1 /\ BecomeLeaderAction => Inv331_R5_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv331_R5_0_I1 /\ ClientRequestAction => Inv331_R5_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv331_R5_0_I1 /\ AdvanceCommitIndexAction => Inv331_R5_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv331_R5_0_I1 /\ AppendEntriesAction => Inv331_R5_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv331_R5_0_I1 /\ HandleRequestVoteRequestAction => Inv331_R5_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv331_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv331_R5_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv331_R5_0_I1 /\ HandleRequestVoteResponseAction => Inv331_R5_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv331_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv331_R5_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv331_R5_0_I1 /\ RejectAppendEntriesRequestAction => Inv331_R5_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv331_R5_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv331_R5_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv331_R5_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv331_R5_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv331_R5_0_I1
  \* (Inv331_R5_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv331_R5_0_I1 /\ HandleAppendEntriesResponseAction => Inv331_R5_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv331_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv774_R1_1_I2
THEOREM L_6 == TypeOK /\ Inv1_R4_0_I1 /\ Inv774_R1_1_I2 /\ Next => Inv774_R1_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv774_R1_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv774_R1_1_I2 /\ RequestVoteAction => Inv774_R1_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv774_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv774_R1_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv774_R1_1_I2 /\ UpdateTermAction => Inv774_R1_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv774_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv774_R1_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv774_R1_1_I2 /\ BecomeLeaderAction => Inv774_R1_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv774_R1_1_I2 /\ ClientRequestAction => Inv774_R1_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv774_R1_1_I2 /\ AdvanceCommitIndexAction => Inv774_R1_1_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv774_R1_1_I2 /\ AppendEntriesAction => Inv774_R1_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv774_R1_1_I2 /\ HandleRequestVoteRequestAction => Inv774_R1_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv774_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv774_R1_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R4_0_I1 /\ Inv774_R1_1_I2 /\ HandleRequestVoteResponseAction => Inv774_R1_1_I2' BY DEF TypeOK,Inv1_R4_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv774_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv774_R1_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv774_R1_1_I2 /\ RejectAppendEntriesRequestAction => Inv774_R1_1_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv774_R1_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv774_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv774_R1_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv774_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv774_R1_1_I2
  \* (Inv774_R1_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv774_R1_1_I2 /\ HandleAppendEntriesResponseAction => Inv774_R1_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv774_R1_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_R4_0_I1
THEOREM L_7 == TypeOK /\ Inv16_R9_0_I1 /\ Inv1_R4_0_I1 /\ Next => Inv1_R4_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1_R4_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1_R4_0_I1 /\ RequestVoteAction => Inv1_R4_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1_R4_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R4_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R4_0_I1 /\ UpdateTermAction => Inv1_R4_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1_R4_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R4_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1_R4_0_I1 /\ BecomeLeaderAction => Inv1_R4_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1_R4_0_I1 /\ ClientRequestAction => Inv1_R4_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1_R4_0_I1 /\ AdvanceCommitIndexAction => Inv1_R4_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1_R4_0_I1 /\ AppendEntriesAction => Inv1_R4_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv16_R9_0_I1 /\ Inv1_R4_0_I1 /\ HandleRequestVoteRequestAction => Inv1_R4_0_I1' BY DEF TypeOK,Inv16_R9_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1_R4_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R4_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R4_0_I1 /\ HandleRequestVoteResponseAction => Inv1_R4_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1_R4_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R4_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1_R4_0_I1 /\ RejectAppendEntriesRequestAction => Inv1_R4_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1_R4_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1_R4_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1_R4_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1_R4_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1_R4_0_I1
  \* (Inv1_R4_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1_R4_0_I1 /\ HandleAppendEntriesResponseAction => Inv1_R4_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1_R4_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv16_R9_0_I1
THEOREM L_8 == TypeOK /\ Inv16_R9_0_I1 /\ Next => Inv16_R9_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv16_R9_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv16_R9_0_I1 /\ RequestVoteAction => Inv16_R9_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv16_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv16_R9_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv16_R9_0_I1 /\ UpdateTermAction => Inv16_R9_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv16_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv16_R9_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv16_R9_0_I1 /\ BecomeLeaderAction => Inv16_R9_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv16_R9_0_I1 /\ ClientRequestAction => Inv16_R9_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv16_R9_0_I1 /\ AdvanceCommitIndexAction => Inv16_R9_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv16_R9_0_I1 /\ AppendEntriesAction => Inv16_R9_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv16_R9_0_I1 /\ HandleRequestVoteRequestAction => Inv16_R9_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv16_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv16_R9_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv16_R9_0_I1 /\ HandleRequestVoteResponseAction => Inv16_R9_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv16_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv16_R9_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv16_R9_0_I1 /\ RejectAppendEntriesRequestAction => Inv16_R9_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv16_R9_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv16_R9_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv16_R9_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv16_R9_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv16_R9_0_I1
  \* (Inv16_R9_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv16_R9_0_I1 /\ HandleAppendEntriesResponseAction => Inv16_R9_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv16_R9_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R5_0_I1
THEOREM L_9 == TypeOK /\ Inv10_R5_0_I1 /\ Next => Inv10_R5_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R5_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R5_0_I1 /\ RequestVoteAction => Inv10_R5_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R5_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R5_0_I1 /\ UpdateTermAction => Inv10_R5_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R5_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_R5_0_I1 /\ BecomeLeaderAction => Inv10_R5_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_R5_0_I1 /\ ClientRequestAction => Inv10_R5_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10_R5_0_I1 /\ AdvanceCommitIndexAction => Inv10_R5_0_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10_R5_0_I1 /\ AppendEntriesAction => Inv10_R5_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R5_0_I1 /\ HandleRequestVoteRequestAction => Inv10_R5_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R5_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv10_R5_0_I1 /\ HandleRequestVoteResponseAction => Inv10_R5_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R5_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R5_0_I1 /\ RejectAppendEntriesRequestAction => Inv10_R5_0_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R5_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R5_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R5_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R5_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R5_0_I1
  \* (Inv10_R5_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R5_0_I1 /\ HandleAppendEntriesResponseAction => Inv10_R5_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R2_1_I1
THEOREM L_10 == TypeOK /\ Inv6_R5_2_I0 /\ Inv10_R2_1_I1 /\ Next => Inv10_R2_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R2_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_1_I1 /\ RequestVoteAction => Inv10_R2_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R2_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R2_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R2_1_I1 /\ UpdateTermAction => Inv10_R2_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R2_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R2_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_R2_1_I1 /\ BecomeLeaderAction => Inv10_R2_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_R2_1_I1 /\ ClientRequestAction => Inv10_R2_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10_R2_1_I1 /\ AdvanceCommitIndexAction => Inv10_R2_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10_R2_1_I1 /\ AppendEntriesAction => Inv10_R2_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R2_1_I1 /\ HandleRequestVoteRequestAction => Inv10_R2_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R2_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R5_2_I0 /\ Inv10_R2_1_I1 /\ HandleRequestVoteResponseAction => Inv10_R2_1_I1' BY DEF TypeOK,Inv6_R5_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R2_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R2_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R2_1_I1 /\ RejectAppendEntriesRequestAction => Inv10_R2_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R2_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R2_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R2_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R2_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R2_1_I1
  \* (Inv10_R2_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R2_1_I1 /\ HandleAppendEntriesResponseAction => Inv10_R2_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R2_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6_R5_2_I0
THEOREM L_11 == TypeOK /\ Inv6_R5_2_I0 /\ Next => Inv6_R5_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_R5_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R5_2_I0 /\ RequestVoteAction => Inv6_R5_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_R5_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R5_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R5_2_I0 /\ UpdateTermAction => Inv6_R5_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_R5_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R5_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_R5_2_I0 /\ BecomeLeaderAction => Inv6_R5_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_R5_2_I0 /\ ClientRequestAction => Inv6_R5_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6_R5_2_I0 /\ AdvanceCommitIndexAction => Inv6_R5_2_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6_R5_2_I0 /\ AppendEntriesAction => Inv6_R5_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R5_2_I0 /\ HandleRequestVoteRequestAction => Inv6_R5_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_R5_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R5_2_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R5_2_I0 /\ HandleRequestVoteResponseAction => Inv6_R5_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_R5_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R5_2_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6_R5_2_I0 /\ RejectAppendEntriesRequestAction => Inv6_R5_2_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6_R5_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv6_R5_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6_R5_2_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6_R5_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6_R5_2_I0
  \* (Inv6_R5_2_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6_R5_2_I0 /\ HandleAppendEntriesResponseAction => Inv6_R5_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_R5_2_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv7_R5_1_I1
THEOREM L_12 == TypeOK /\ Inv10_R5_0_I1 /\ Inv7_R5_1_I1 /\ Next => Inv7_R5_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_R5_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_R5_1_I1 /\ RequestVoteAction => Inv7_R5_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_R5_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_R5_1_I1 /\ UpdateTermAction => Inv7_R5_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_R5_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_R5_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_R5_1_I1 /\ BecomeLeaderAction => Inv7_R5_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_R5_1_I1 /\ ClientRequestAction => Inv7_R5_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv7_R5_1_I1 /\ AdvanceCommitIndexAction => Inv7_R5_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv7_R5_1_I1 /\ AppendEntriesAction => Inv7_R5_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R5_0_I1 /\ Inv7_R5_1_I1 /\ HandleRequestVoteRequestAction => Inv7_R5_1_I1' BY DEF TypeOK,Inv10_R5_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_R5_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv7_R5_1_I1 /\ HandleRequestVoteResponseAction => Inv7_R5_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R5_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_R5_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv7_R5_1_I1 /\ RejectAppendEntriesRequestAction => Inv7_R5_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv7_R5_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv7_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv7_R5_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv7_R5_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv7_R5_1_I1
  \* (Inv7_R5_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv7_R5_1_I1 /\ HandleAppendEntriesResponseAction => Inv7_R5_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_R5_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv25049_R1_1_I2
THEOREM L_13 == TypeOK /\ Inv10_R2_1_I1 /\ Inv2197_R3_0_I2 /\ Inv5439_R3_0_I2 /\ Inv25049_R1_1_I2 /\ Next => Inv25049_R1_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv25049_R1_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_1_I1 /\ Inv25049_R1_1_I2 /\ RequestVoteAction => Inv25049_R1_1_I2' BY DEF TypeOK,Inv10_R2_1_I1,RequestVoteAction,RequestVote,Inv25049_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv25049_R1_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv25049_R1_1_I2 /\ UpdateTermAction => Inv25049_R1_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv25049_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv25049_R1_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv25049_R1_1_I2 /\ BecomeLeaderAction => Inv25049_R1_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv25049_R1_1_I2 /\ ClientRequestAction => Inv25049_R1_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv25049_R1_1_I2 /\ AdvanceCommitIndexAction => Inv25049_R1_1_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv25049_R1_1_I2 /\ AppendEntriesAction => Inv25049_R1_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv25049_R1_1_I2 /\ HandleRequestVoteRequestAction => Inv25049_R1_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv25049_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv25049_R1_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv2197_R3_0_I2 /\ Inv5439_R3_0_I2 /\ Inv25049_R1_1_I2 /\ HandleRequestVoteResponseAction => Inv25049_R1_1_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv2197_R3_0_I2 /\ Inv5439_R3_0_I2 /\ Inv25049_R1_1_I2 /\ HandleRequestVoteResponseAction,
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((currentTerm[VARI] >= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~((state[VARJ] \in {Leader,Candidate} /\ VARI # VARJ)))))'
      BY DEF Inv25049_R1_1_I2
    <2> QED
      <3> SUFFICES ASSUME NEW m \in requestVoteResponseMsgs,
                          HandleRequestVoteResponse(m)
                   PROVE  (~((currentTerm[VARI] >= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])) \/ (~((state[VARJ] \in {Leader,Candidate} /\ VARI # VARJ)))))'
        BY DEF HandleRequestVoteResponseAction
      <3> QED
        BY FS_Singleton, FS_Union, FS_Subset, FS_Difference DEF TypeOK,Inv2197_R3_0_I2,Inv5439_R3_0_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv25049_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
  \* (Inv25049_R1_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv25049_R1_1_I2 /\ RejectAppendEntriesRequestAction => Inv25049_R1_1_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv25049_R1_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv25049_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv25049_R1_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv25049_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv25049_R1_1_I2
  \* (Inv25049_R1_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv25049_R1_1_I2 /\ HandleAppendEntriesResponseAction => Inv25049_R1_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv25049_R1_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv2197_R3_0_I2
THEOREM L_14 == TypeOK /\ Inv6_R5_2_I0 /\ Inv6_R5_2_I0 /\ Inv331_R5_0_I1 /\ Inv2197_R3_0_I2 /\ Next => Inv2197_R3_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2197_R3_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R5_2_I0 /\ Inv2197_R3_0_I2 /\ RequestVoteAction => Inv2197_R3_0_I2' BY DEF TypeOK,Inv6_R5_2_I0,RequestVoteAction,RequestVote,Inv2197_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2197_R3_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R5_2_I0 /\ Inv2197_R3_0_I2 /\ UpdateTermAction => Inv2197_R3_0_I2' BY DEF TypeOK,Inv6_R5_2_I0,UpdateTermAction,UpdateTerm,Inv2197_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2197_R3_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2197_R3_0_I2 /\ BecomeLeaderAction => Inv2197_R3_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv2197_R3_0_I2 /\ ClientRequestAction => Inv2197_R3_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv2197_R3_0_I2 /\ AdvanceCommitIndexAction => Inv2197_R3_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv2197_R3_0_I2 /\ AppendEntriesAction => Inv2197_R3_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv331_R5_0_I1 /\ Inv2197_R3_0_I2 /\ HandleRequestVoteRequestAction => Inv2197_R3_0_I2' BY DEF TypeOK,Inv331_R5_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2197_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2197_R3_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv2197_R3_0_I2 /\ HandleRequestVoteResponseAction => Inv2197_R3_0_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2197_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2197_R3_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv2197_R3_0_I2 /\ RejectAppendEntriesRequestAction => Inv2197_R3_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv2197_R3_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv2197_R3_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv2197_R3_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv2197_R3_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv2197_R3_0_I2
  \* (Inv2197_R3_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv2197_R3_0_I2 /\ HandleAppendEntriesResponseAction => Inv2197_R3_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2197_R3_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5439_R3_0_I2
THEOREM L_15 == TypeOK /\ Inv6_R5_2_I0 /\ Inv6_R5_2_I0 /\ Inv5439_R3_0_I2 /\ Next => Inv5439_R3_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5439_R3_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5439_R3_0_I2 /\ RequestVoteAction => Inv5439_R3_0_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5439_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5439_R3_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R5_2_I0 /\ Inv5439_R3_0_I2 /\ UpdateTermAction => Inv5439_R3_0_I2' BY DEF TypeOK,Inv6_R5_2_I0,UpdateTermAction,UpdateTerm,Inv5439_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5439_R3_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5439_R3_0_I2 /\ BecomeLeaderAction => Inv5439_R3_0_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5439_R3_0_I2
  \* (Inv5439_R3_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv5439_R3_0_I2 /\ ClientRequestAction => Inv5439_R3_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5439_R3_0_I2
  \* (Inv5439_R3_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv5439_R3_0_I2 /\ AdvanceCommitIndexAction => Inv5439_R3_0_I2' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv5439_R3_0_I2
  \* (Inv5439_R3_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv5439_R3_0_I2 /\ AppendEntriesAction => Inv5439_R3_0_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5439_R3_0_I2
  \* (Inv5439_R3_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv5439_R3_0_I2 /\ HandleRequestVoteRequestAction => Inv5439_R3_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5439_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5439_R3_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv5439_R3_0_I2 /\ HandleRequestVoteResponseAction => Inv5439_R3_0_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5439_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5439_R3_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv5439_R3_0_I2 /\ RejectAppendEntriesRequestAction => Inv5439_R3_0_I2' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv5439_R3_0_I2
  \* (Inv5439_R3_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv5439_R3_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv5439_R3_0_I2' 
    <2> SUFFICES ASSUME TypeOK /\ Inv5439_R3_0_I2 /\ AcceptAppendEntriesRequestAppendAction,
                        NEW VARI \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (((state[VARI] = Leader)) \/ (~((state[VARI] = Follower))) \/ ((currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)))'
      BY DEF Inv5439_R3_0_I2
    <2> QED
      <3> SUFFICES ASSUME NEW m \in appendEntriesRequestMsgs,
                          AcceptAppendEntriesRequestAppend(m)
                   PROVE  (((state[VARI] = Leader)) \/ (~((state[VARI] = Follower))) \/ ((currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)))'
        BY DEF AcceptAppendEntriesRequestAppendAction
      <3> QED
        BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5439_R3_0_I2
      
  \* (Inv5439_R3_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6_R5_2_I0 /\ Inv5439_R3_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv5439_R3_0_I2' BY DEF TypeOK,Inv6_R5_2_I0,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv5439_R3_0_I2
  \* (Inv5439_R3_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv5439_R3_0_I2 /\ HandleAppendEntriesResponseAction => Inv5439_R3_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5439_R3_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
    <1>2. Init => Inv20249_R0_0_I2 BY DEF Init, Inv20249_R0_0_I2, IndGlobal
    <1>3. Init => Inv10820_R1_0_I2 BY DEF Init, Inv10820_R1_0_I2, IndGlobal
    <1>4. Init => Inv22_R2_0_I1 BY DEF Init, Inv22_R2_0_I1, IndGlobal
    <1>5. Init => Inv331_R5_0_I1 BY DEF Init, Inv331_R5_0_I1, IndGlobal
    <1>6. Init => Inv774_R1_1_I2 BY DEF Init, Inv774_R1_1_I2, IndGlobal
    <1>7. Init => Inv1_R4_0_I1 BY DEF Init, Inv1_R4_0_I1, IndGlobal
    <1>8. Init => Inv16_R9_0_I1 BY DEF Init, Inv16_R9_0_I1, IndGlobal
    <1>9. Init => Inv10_R5_0_I1 BY DEF Init, Inv10_R5_0_I1, IndGlobal
    <1>10. Init => Inv10_R2_1_I1 BY DEF Init, Inv10_R2_1_I1, IndGlobal
    <1>11. Init => Inv6_R5_2_I0 BY DEF Init, Inv6_R5_2_I0, IndGlobal
    <1>12. Init => Inv7_R5_1_I1 BY DEF Init, Inv7_R5_1_I1, IndGlobal
    <1>13. Init => Inv25049_R1_1_I2 BY DEF Init, Inv25049_R1_1_I2, IndGlobal
    <1>14. Init => Inv2197_R3_0_I2 BY DEF Init, Inv2197_R3_0_I2, IndGlobal
    <1>15. Init => Inv5439_R3_0_I2 BY DEF Init, Inv5439_R3_0_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15 DEF Next, IndGlobal

====