--------------------------------- MODULE AsyncRaft_IndProofs_PrimaryHasEntriesItCreated ---------------------------------
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

\* Proof Graph Stats
\* ==================
\* seed: 7
\* num proof graph nodes: 40
\* num proof obligations: 360
Safety == H_PrimaryHasEntriesItCreated
Inv8509_2dd8_R0_0_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : \A VARLOGINDI \in LogIndices : (VARMAEREQ.mentries # <<>> /\ VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = VARMAEREQ.mentries[1]) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI] /\ state[VARI] = Leader)) \/ (~(VARLOGINDI = VARMAEREQ.mprevLogIndex + 1))
Inv5215_bcfb_R0_1_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum)))
Inv5_404d_R0_2_I1 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader)))
Inv6390_7e0d_R1_1_I2 == \A VARI \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum)))
Inv6746_404d_R2_1_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum))
Inv8096_c721_R2_2_I2 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARI] = Candidate)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs))
Inv7767_5b71_R4_1_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARMAEREQ \in appendEntriesRequestMsgs : ~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI])))
Inv2_8e53_R5_0_I0 == (\A s,t \in Server : ( /\ s # t /\ state[s] \in {Leader,Candidate} /\ state[t] \in {Leader,Candidate} /\ currentTerm[s] = currentTerm[t]) => votesGranted[s] \cap votesGranted[t] = {})
Inv9_928b_R5_1_I2 == \A VARI \in Server : (VARI \in votesGranted[VARI]) \/ ((votesGranted[VARI] = {}))
Inv1630_58c9_R5_1_I2 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARJ] > currentTerm[VARI])) \/ (~((state[VARJ] \in {Leader,Candidate} /\ VARI # VARJ))) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv5771_fffd_R5_1_I2 == \A VARJ \in Server : ((state[VARJ] = Follower)) \/ (~((state[VARJ] = Leader))) \/ ((votesGranted[VARJ] \in Quorum))
Inv4_42ac_R5_1_I2 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv13_6261_R6_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((VARI \in votesGranted[VARI]))
Inv138_3acc_R6_1_I1 == \A VARI \in Server : (votesGranted[VARI] \in Quorum) \/ (~((state[VARI] = Leader)))
Inv5_c57a_R6_2_I1 == (H_LogEntryInTermImpliesSafeAtTerm /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor)
Inv607_376d_R6_2_I1 == \A VARI \in Server : \A VARJ \in Server : ~((state[VARJ] \in {Leader,Candidate} /\ VARI # VARJ)) \/ (~(votedFor[VARJ] = VARI))
Inv7_1e2e_R6_3_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.mdest] >= VARREQVRES.mterm) \/ (~(VARREQVRES.mvoteGranted))
Inv84_4aa6_R7_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] # Nil /\ VARI \in votesGranted[votedFor[VARI]]))
Inv0_2c32_R8_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv387_09bb_R9_0_I1 == \A VARI \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {}))
Inv11_f533_R10_0_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv2_e30e_R12_0_I1 == \A VARI \in Server : ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower)))
Inv7_82b3_R12_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv7_2014_R15_0_I1 == (H_LogEntryInTermImpliesSafeAtTermAppendEntries /\ currentTerm = currentTerm /\ state = state /\ log = log /\ votedFor = votedFor /\ appendEntriesRequestMsgs = appendEntriesRequestMsgs)
Inv31_73fd_R15_1_I1 == \A VARI \in Server : ((state[VARI] = Follower)) \/ ((votedFor[VARI] = VARI))
Inv11_dadc_R15_1_I1 == \A VARI \in Server : ((votedFor[VARI] = VARI)) => ((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) 
Inv107_791e_R15_2_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted) \/ (~(votedFor[VARJ] = VARI))
Inv3_9e78_R17_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)
Inv15_1f30_R18_0_I1 == \A VARJ \in Server : ((state[VARJ] = Follower)) \/ ((votedFor[VARJ] = VARJ))
Inv81_fe26_R20_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : (VARREQVM.msource = VARI) => (~(votesGranted[VARI] = {}))
Inv13_3715_R22_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)
Inv12_0a54_R24_0_I1 == \A VARI \in Server : ~((commitIndex[VARI] > 0))
Inv379_f624_R24_0_I1 == \A VARI \in Server : (H_QuorumsSafeAtTerms /\ currentTerm = currentTerm /\ state = state /\ votedFor = votedFor) \/ (~((state[VARI] = Leader)))
Inv18_bf9f_R24_0_I1 == \A VARI \in Server : \A VARLOGINDI \in LogIndices : ~(VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] > currentTerm[VARI])
Inv17_e2fa_R26_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : ~(VARREQVM.mdest = VARI) \/ (~(VARREQVM.msource = VARI))
Inv21_3b9d_R26_2_I1 == \A VARI \in Server : ~((state[VARI] = Follower)) \/ (~(votedFor[VARI] = VARI))
Inv10303_8d53_R26_3_I2 == \A VARI \in Server : \A VARJ \in Server : ~((currentTerm[VARI] > currentTerm[VARJ])) \/ (~(VARJ \in votesGranted[VARI]) \/ (~(votedFor[VARI] = VARI)))
Inv0_5020_R27_1_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~(votedFor[VARI] = VARJ))
Inv6_9fea_R34_0_I1 == \A VARMAEREQ \in appendEntriesRequestMsgs : (VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] <= VARMAEREQ.mterm) \/ ((VARMAEREQ.mentries = <<>>))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv8509_2dd8_R0_0_I2
  /\ Inv6390_7e0d_R1_1_I2
  /\ Inv5215_bcfb_R0_1_I2
  /\ Inv6746_404d_R2_1_I2
  /\ Inv2_8e53_R5_0_I0
  /\ Inv4_42ac_R5_1_I2
  /\ Inv2_e30e_R12_0_I1
  /\ Inv13_3715_R22_0_I0
  /\ Inv11_f533_R10_0_I0
  /\ Inv0_2c32_R8_1_I1
  /\ Inv7_82b3_R12_1_I0
  /\ Inv9_928b_R5_1_I2
  /\ Inv387_09bb_R9_0_I1
  /\ Inv81_fe26_R20_0_I1
  /\ Inv1630_58c9_R5_1_I2
  /\ Inv13_6261_R6_1_I1
  /\ Inv5771_fffd_R5_1_I2
  /\ Inv8096_c721_R2_2_I2
  /\ Inv138_3acc_R6_1_I1
  /\ Inv5_c57a_R6_2_I1
  /\ Inv7_2014_R15_0_I1
  /\ Inv12_0a54_R24_0_I1
  /\ Inv379_f624_R24_0_I1
  /\ Inv31_73fd_R15_1_I1
  /\ Inv10303_8d53_R26_3_I2
  /\ Inv17_e2fa_R26_0_I1
  /\ Inv11_dadc_R15_1_I1
  /\ Inv21_3b9d_R26_2_I1
  /\ Inv18_bf9f_R24_0_I1
  /\ Inv6_9fea_R34_0_I1
  /\ Inv107_791e_R15_2_I1
  /\ Inv3_9e78_R17_0_I0
  /\ Inv0_5020_R27_1_I1
  /\ Inv607_376d_R6_2_I1
  /\ Inv7_1e2e_R6_3_I1
  /\ Inv7767_5b71_R4_1_I2
  /\ Inv84_4aa6_R7_1_I1
  /\ Inv15_1f30_R18_0_I1
  /\ Inv5_404d_R0_2_I1


\* mean in-degree: 2.275
\* median in-degree: 1
\* max in-degree: 10
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
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF AppendEntriesRequestType, AppendEntriesResponseType, LastTerm
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RequestVoteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      <3> SUFFICES ASSUME NEW i \in Server,
                          RequestVote(i)
                   PROVE  (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
        BY DEF RequestVoteAction
      <3> QED
        BY FS_Subset DEF LastTerm, TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
      
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
      BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK, Min
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
      <3> SUFFICES ASSUME NEW m \in requestVoteRequestMsgs,
                          HandleRequestVoteRequest(m)
                   PROVE  (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
        BY DEF HandleRequestVoteRequestAction
      <3> QED
        <4> SUFFICES ASSUME NEW m_1 \in requestVoteRequestMsgs,
                            HandleRequestVoteRequest(m_1)
                     PROVE  (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
          BY DEF HandleRequestVoteRequestAction
        <4> QED
          BY FS_Singleton, FS_Difference, FS_Subset DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
      
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
      BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,TypeOK
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
  <1>9. TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleAppendEntriesResponseAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>3. (appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>4. (appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>5. (currentTerm \in [Server -> Nat])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>6. (state       \in [Server -> {Leader, Follower, Candidate}])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>7. (votedFor    \in [Server -> ({Nil} \cup Server)])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>8. (votesGranted \in [Server -> (SUBSET Server)])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>9. (nextIndex  \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>10. (matchIndex \in [Server -> [Server -> Nat]])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>11. (log             \in [Server -> Seq(Nat)])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>12. (commitIndex     \in [Server -> Nat])'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>13. (\A m \in requestVoteRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>14. (\A m \in requestVoteResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>15. (\A m \in appendEntriesRequestMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>16. (\A m \in appendEntriesResponseMsgs : m.msource # m.mdest)'
      BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,TypeOK
    <2>17. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, <2>16, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ Inv5_404d_R0_2_I1 /\ Inv8509_2dd8_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_PrimaryHasEntriesItCreated
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety' BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ Safety /\ BecomeLeaderAction => H_PrimaryHasEntriesItCreated' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv5215_bcfb_R0_1_I2,
                        Safety,
                        TRUE,
                        NEW i_1 \in Server,
                        BecomeLeader(i_1),
                        NEW i \in Server', NEW j \in Server',
                        (state[i] = Leader)'
                 PROVE  (~(\E k \in DOMAIN log[j] :
                             /\ log[j][k] = currentTerm[i]
                             /\ ~\E ind \in DOMAIN log[i] : (ind = k /\ log[i][k] = log[j][k]) 
                             ))'
      BY DEF BecomeLeaderAction, H_PrimaryHasEntriesItCreated
    <2> QED
      BY DEF TypeOK,Inv5215_bcfb_R0_1_I2,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_404d_R0_2_I1 /\ Safety /\ ClientRequestAction => Safety' BY DEF TypeOK,Inv5_404d_R0_2_I1,ClientRequestAction,ClientRequest,Safety,H_OnePrimaryPerTerm
  \* (Safety,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ AppendEntriesAction => Safety' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ Safety /\ AcceptAppendEntriesRequestAppendAction => H_PrimaryHasEntriesItCreated' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8509_2dd8_R0_0_I2,
                        Safety,
                        NEW m \in appendEntriesRequestMsgs,
                        AcceptAppendEntriesRequestAppend(m),
                        NEW i \in Server', NEW j \in Server',
                        (state[i] = Leader)'
                 PROVE  (~(\E k \in DOMAIN log[j] :
                             /\ log[j][k] = currentTerm[i]
                             /\ ~\E ind \in DOMAIN log[i] : (ind = k /\ log[i][k] = log[j][k]) 
                             ))'
      BY DEF AcceptAppendEntriesRequestAppendAction, H_PrimaryHasEntriesItCreated
    <2> QED
      BY DEF TypeOK,Inv8509_2dd8_R0_0_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,H_OnePrimaryPerTerm
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,H_OnePrimaryPerTerm
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next, Safety


\*** Inv8509_2dd8_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ Safety /\ Inv8509_2dd8_R0_0_I2 /\ Next => Inv8509_2dd8_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8509_2dd8_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ RequestVoteAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv8509_2dd8_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8509_2dd8_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ UpdateTermAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8509_2dd8_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8509_2dd8_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ Inv8509_2dd8_R0_0_I2 /\ BecomeLeaderAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,Inv6390_7e0d_R1_1_I2,BecomeLeaderAction,BecomeLeader,Inv8509_2dd8_R0_0_I2
  \* (Inv8509_2dd8_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ ClientRequestAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8509_2dd8_R0_0_I2
  \* (Inv8509_2dd8_R0_0_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Safety /\ Inv8509_2dd8_R0_0_I2 /\ AppendEntriesAction => Inv8509_2dd8_R0_0_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Safety,
                        Inv8509_2dd8_R0_0_I2,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARI \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs',
                        NEW VARLOGINDI \in LogIndices'
                 PROVE  ((VARMAEREQ.mentries # <<>> /\ VARLOGINDI \in DOMAIN log[VARI] /\ log[VARI][VARLOGINDI] = VARMAEREQ.mentries[1]) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI] /\ state[VARI] = Leader)) \/ (~(VARLOGINDI = VARMAEREQ.mprevLogIndex + 1)))'
      BY DEF AppendEntriesAction, Inv8509_2dd8_R0_0_I2
    <2> QED
      BY DEF TypeOK,Safety,AppendEntriesAction,AppendEntries,Inv8509_2dd8_R0_0_I2
  \* (Inv8509_2dd8_R0_0_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8509_2dd8_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8509_2dd8_R0_0_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8509_2dd8_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8509_2dd8_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8509_2dd8_R0_0_I2
  \* (Inv8509_2dd8_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8509_2dd8_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv8509_2dd8_R0_0_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8509_2dd8_R0_0_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6390_7e0d_R1_1_I2
THEOREM L_3 == TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ Inv7767_5b71_R4_1_I2 /\ Inv6390_7e0d_R1_1_I2 /\ Next => Inv6390_7e0d_R1_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6390_7e0d_R1_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ RequestVoteAction => Inv6390_7e0d_R1_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6390_7e0d_R1_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF Inv6390_7e0d_R1_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6390_7e0d_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6390_7e0d_R1_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ UpdateTermAction => Inv6390_7e0d_R1_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6390_7e0d_R1_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6390_7e0d_R1_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ BecomeLeaderAction => Inv6390_7e0d_R1_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6390_7e0d_R1_1_I2
  \* (Inv6390_7e0d_R1_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ ClientRequestAction => Inv6390_7e0d_R1_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6390_7e0d_R1_1_I2
  \* (Inv6390_7e0d_R1_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ Inv6390_7e0d_R1_1_I2 /\ AppendEntriesAction => Inv6390_7e0d_R1_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv5215_bcfb_R0_1_I2,
                        Inv6390_7e0d_R1_1_I2,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARI \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF AppendEntriesAction, Inv6390_7e0d_R1_1_I2
    <2> QED
      BY DEF TypeOK,Inv5215_bcfb_R0_1_I2,AppendEntriesAction,AppendEntries,Inv6390_7e0d_R1_1_I2
  \* (Inv6390_7e0d_R1_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ HandleRequestVoteRequestAction => Inv6390_7e0d_R1_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6390_7e0d_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6390_7e0d_R1_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ Inv6390_7e0d_R1_1_I2 /\ HandleRequestVoteResponseAction => Inv6390_7e0d_R1_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv7767_5b71_R4_1_I2,
                        Inv6390_7e0d_R1_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate)) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF HandleRequestVoteResponseAction, Inv6390_7e0d_R1_1_I2
    <2> QED
      BY DEF TypeOK,Inv7767_5b71_R4_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6390_7e0d_R1_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6390_7e0d_R1_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6390_7e0d_R1_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6390_7e0d_R1_1_I2
  \* (Inv6390_7e0d_R1_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ HandleAppendEntriesResponseAction => Inv6390_7e0d_R1_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6390_7e0d_R1_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5215_bcfb_R0_1_I2
THEOREM L_4 == TypeOK /\ Inv6746_404d_R2_1_I2 /\ Inv8096_c721_R2_2_I2 /\ Inv6390_7e0d_R1_1_I2 /\ Inv5215_bcfb_R0_1_I2 /\ Next => Inv5215_bcfb_R0_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5215_bcfb_R0_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ RequestVoteAction => Inv5215_bcfb_R0_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv5215_bcfb_R0_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF Inv5215_bcfb_R0_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5215_bcfb_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5215_bcfb_R0_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ UpdateTermAction => Inv5215_bcfb_R0_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5215_bcfb_R0_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5215_bcfb_R0_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ BecomeLeaderAction => Inv5215_bcfb_R0_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5215_bcfb_R0_1_I2
  \* (Inv5215_bcfb_R0_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6746_404d_R2_1_I2 /\ Inv5215_bcfb_R0_1_I2 /\ ClientRequestAction => Inv5215_bcfb_R0_1_I2' BY DEF TypeOK,Inv6746_404d_R2_1_I2,ClientRequestAction,ClientRequest,Inv5215_bcfb_R0_1_I2
  \* (Inv5215_bcfb_R0_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ AppendEntriesAction => Inv5215_bcfb_R0_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5215_bcfb_R0_1_I2
  \* (Inv5215_bcfb_R0_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ HandleRequestVoteRequestAction => Inv5215_bcfb_R0_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5215_bcfb_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5215_bcfb_R0_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8096_c721_R2_2_I2 /\ Inv5215_bcfb_R0_1_I2 /\ HandleRequestVoteResponseAction => Inv5215_bcfb_R0_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8096_c721_R2_2_I2,
                        Inv5215_bcfb_R0_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF HandleRequestVoteResponseAction, Inv5215_bcfb_R0_1_I2
    <2> QED
      BY DEF TypeOK,Inv8096_c721_R2_2_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5215_bcfb_R0_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5215_bcfb_R0_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ Inv5215_bcfb_R0_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv5215_bcfb_R0_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6390_7e0d_R1_1_I2,
                        Inv5215_bcfb_R0_1_I2,
                        NEW m \in appendEntriesRequestMsgs,
                        AcceptAppendEntriesRequestAppend(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI]) \/ (~(votesGranted[VARI] \in Quorum))))'
      BY DEF AcceptAppendEntriesRequestAppendAction, Inv5215_bcfb_R0_1_I2
    <2> QED
      BY DEF TypeOK,Inv6390_7e0d_R1_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5215_bcfb_R0_1_I2
  \* (Inv5215_bcfb_R0_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5215_bcfb_R0_1_I2 /\ HandleAppendEntriesResponseAction => Inv5215_bcfb_R0_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5215_bcfb_R0_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6746_404d_R2_1_I2
THEOREM L_5 == TypeOK /\ Inv2_8e53_R5_0_I0 /\ Inv9_928b_R5_1_I2 /\ Inv1630_58c9_R5_1_I2 /\ Inv5771_fffd_R5_1_I2 /\ Inv4_42ac_R5_1_I2 /\ Inv6746_404d_R2_1_I2 /\ Next => Inv6746_404d_R2_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6746_404d_R2_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv6746_404d_R2_1_I2 /\ RequestVoteAction => Inv6746_404d_R2_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv6746_404d_R2_1_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Leader))) \/ (~(votesGranted[VARI] \in Quorum)))'
      BY DEF Inv6746_404d_R2_1_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6746_404d_R2_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6746_404d_R2_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6746_404d_R2_1_I2 /\ UpdateTermAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6746_404d_R2_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6746_404d_R2_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2_8e53_R5_0_I0 /\ Inv6746_404d_R2_1_I2 /\ BecomeLeaderAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,Inv2_8e53_R5_0_I0,BecomeLeaderAction,BecomeLeader,Inv6746_404d_R2_1_I2
  \* (Inv6746_404d_R2_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6746_404d_R2_1_I2 /\ ClientRequestAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6746_404d_R2_1_I2
  \* (Inv6746_404d_R2_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv6746_404d_R2_1_I2 /\ AppendEntriesAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6746_404d_R2_1_I2
  \* (Inv6746_404d_R2_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6746_404d_R2_1_I2 /\ HandleRequestVoteRequestAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6746_404d_R2_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6746_404d_R2_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv9_928b_R5_1_I2 /\ Inv1630_58c9_R5_1_I2 /\ Inv5771_fffd_R5_1_I2 /\ Inv4_42ac_R5_1_I2 /\ Inv6746_404d_R2_1_I2 /\ HandleRequestVoteResponseAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,Inv9_928b_R5_1_I2,Inv1630_58c9_R5_1_I2,Inv5771_fffd_R5_1_I2,Inv4_42ac_R5_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6746_404d_R2_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6746_404d_R2_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6746_404d_R2_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6746_404d_R2_1_I2
  \* (Inv6746_404d_R2_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6746_404d_R2_1_I2 /\ HandleAppendEntriesResponseAction => Inv6746_404d_R2_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6746_404d_R2_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2_8e53_R5_0_I0
THEOREM L_6 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv4_42ac_R5_1_I2 /\ Inv2_8e53_R5_0_I0 /\ Next => Inv2_8e53_R5_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2_8e53_R5_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv2_8e53_R5_0_I0 /\ RequestVoteAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv2_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2_8e53_R5_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv2_8e53_R5_0_I0 /\ UpdateTermAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv2_8e53_R5_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2_8e53_R5_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2_8e53_R5_0_I0 /\ BecomeLeaderAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2_8e53_R5_0_I0
  \* (Inv2_8e53_R5_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv2_8e53_R5_0_I0 /\ ClientRequestAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2_8e53_R5_0_I0
  \* (Inv2_8e53_R5_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv2_8e53_R5_0_I0 /\ AppendEntriesAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2_8e53_R5_0_I0
  \* (Inv2_8e53_R5_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2_8e53_R5_0_I0 /\ HandleRequestVoteRequestAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2_8e53_R5_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv4_42ac_R5_1_I2 /\ Inv2_8e53_R5_0_I0 /\ HandleRequestVoteResponseAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,Inv4_42ac_R5_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2_8e53_R5_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2_8e53_R5_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv2_8e53_R5_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2_8e53_R5_0_I0
  \* (Inv2_8e53_R5_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv2_8e53_R5_0_I0 /\ HandleAppendEntriesResponseAction => Inv2_8e53_R5_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2_8e53_R5_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv4_42ac_R5_1_I2
THEOREM L_7 == TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv2_e30e_R12_0_I1 /\ Inv7_82b3_R12_1_I0 /\ Inv4_42ac_R5_1_I2 /\ Next => Inv4_42ac_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv4_42ac_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv4_42ac_R5_1_I2 /\ RequestVoteAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,Inv11_f533_R10_0_I0,RequestVoteAction,RequestVote,Inv4_42ac_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_42ac_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv4_42ac_R5_1_I2 /\ UpdateTermAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv4_42ac_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv4_42ac_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv4_42ac_R5_1_I2 /\ BecomeLeaderAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv4_42ac_R5_1_I2
  \* (Inv4_42ac_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv4_42ac_R5_1_I2 /\ ClientRequestAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv4_42ac_R5_1_I2
  \* (Inv4_42ac_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv4_42ac_R5_1_I2 /\ AppendEntriesAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv4_42ac_R5_1_I2
  \* (Inv4_42ac_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2_e30e_R12_0_I1 /\ Inv4_42ac_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,Inv2_e30e_R12_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv4_42ac_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_42ac_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_82b3_R12_1_I0 /\ Inv4_42ac_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,Inv7_82b3_R12_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv4_42ac_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv4_42ac_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv4_42ac_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv4_42ac_R5_1_I2
  \* (Inv4_42ac_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv4_42ac_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv4_42ac_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv4_42ac_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv2_e30e_R12_0_I1
THEOREM L_8 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv13_3715_R22_0_I0 /\ Inv2_e30e_R12_0_I1 /\ Next => Inv2_e30e_R12_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv2_e30e_R12_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv2_e30e_R12_0_I1 /\ RequestVoteAction => Inv2_e30e_R12_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_2c32_R8_1_I1,
                        Inv2_e30e_R12_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF Inv2_e30e_R12_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv2_e30e_R12_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2_e30e_R12_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv2_e30e_R12_0_I1 /\ UpdateTermAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,Inv0_2c32_R8_1_I1,UpdateTermAction,UpdateTerm,Inv2_e30e_R12_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv2_e30e_R12_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv2_e30e_R12_0_I1 /\ BecomeLeaderAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv2_e30e_R12_0_I1
  \* (Inv2_e30e_R12_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv2_e30e_R12_0_I1 /\ ClientRequestAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv2_e30e_R12_0_I1
  \* (Inv2_e30e_R12_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv2_e30e_R12_0_I1 /\ AppendEntriesAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv2_e30e_R12_0_I1
  \* (Inv2_e30e_R12_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv2_e30e_R12_0_I1 /\ HandleRequestVoteRequestAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv2_e30e_R12_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2_e30e_R12_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_3715_R22_0_I0 /\ Inv2_e30e_R12_0_I1 /\ HandleRequestVoteResponseAction => Inv2_e30e_R12_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv13_3715_R22_0_I0,
                        Inv2_e30e_R12_0_I1,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARI \in Server'
                 PROVE  (((\A t \in votesGranted[VARI] : /\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI )) \/ (((state[VARI] = Follower))))'
      BY DEF HandleRequestVoteResponseAction, Inv2_e30e_R12_0_I1
    <2> QED
      BY DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv2_e30e_R12_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv2_e30e_R12_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv2_e30e_R12_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv2_e30e_R12_0_I1
  \* (Inv2_e30e_R12_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv2_e30e_R12_0_I1 /\ HandleAppendEntriesResponseAction => Inv2_e30e_R12_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv2_e30e_R12_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv13_3715_R22_0_I0
THEOREM L_9 == TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv11_f533_R10_0_I0 /\ Inv13_3715_R22_0_I0 /\ Next => Inv13_3715_R22_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv13_3715_R22_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv13_3715_R22_0_I0 /\ RequestVoteAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,Inv11_f533_R10_0_I0,RequestVoteAction,RequestVote,Inv13_3715_R22_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_3715_R22_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv13_3715_R22_0_I0 /\ UpdateTermAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,Inv11_f533_R10_0_I0,UpdateTermAction,UpdateTerm,Inv13_3715_R22_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_3715_R22_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv13_3715_R22_0_I0 /\ BecomeLeaderAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv13_3715_R22_0_I0
  \* (Inv13_3715_R22_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv13_3715_R22_0_I0 /\ ClientRequestAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv13_3715_R22_0_I0
  \* (Inv13_3715_R22_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv13_3715_R22_0_I0 /\ AppendEntriesAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv13_3715_R22_0_I0
  \* (Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_3715_R22_0_I0 /\ HandleRequestVoteRequestAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv13_3715_R22_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_3715_R22_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_3715_R22_0_I0 /\ HandleRequestVoteResponseAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv13_3715_R22_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_3715_R22_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_3715_R22_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv13_3715_R22_0_I0
  \* (Inv13_3715_R22_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv13_3715_R22_0_I0 /\ HandleAppendEntriesResponseAction => Inv13_3715_R22_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv13_3715_R22_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_f533_R10_0_I0
THEOREM L_10 == TypeOK /\ Inv11_f533_R10_0_I0 /\ Next => Inv11_f533_R10_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_f533_R10_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv11_f533_R10_0_I0 /\ RequestVoteAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv11_f533_R10_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_f533_R10_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv11_f533_R10_0_I0 /\ UpdateTermAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv11_f533_R10_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_f533_R10_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_f533_R10_0_I0 /\ BecomeLeaderAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_f533_R10_0_I0
  \* (Inv11_f533_R10_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_f533_R10_0_I0 /\ ClientRequestAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_f533_R10_0_I0
  \* (Inv11_f533_R10_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_f533_R10_0_I0 /\ AppendEntriesAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_f533_R10_0_I0
  \* (Inv11_f533_R10_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv11_f533_R10_0_I0 /\ HandleRequestVoteRequestAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_f533_R10_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_f533_R10_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_f533_R10_0_I0 /\ HandleRequestVoteResponseAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_f533_R10_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_f533_R10_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11_f533_R10_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_f533_R10_0_I0
  \* (Inv11_f533_R10_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_f533_R10_0_I0 /\ HandleAppendEntriesResponseAction => Inv11_f533_R10_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_f533_R10_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_2c32_R8_1_I1
THEOREM L_11 == TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv0_2c32_R8_1_I1 /\ Next => Inv0_2c32_R8_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_2c32_R8_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ RequestVoteAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_2c32_R8_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_2c32_R8_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_2c32_R8_1_I1 /\ UpdateTermAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_2c32_R8_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_2c32_R8_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_2c32_R8_1_I1 /\ BecomeLeaderAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_2c32_R8_1_I1 /\ ClientRequestAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv0_2c32_R8_1_I1 /\ AppendEntriesAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv0_2c32_R8_1_I1 /\ HandleRequestVoteRequestAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_2c32_R8_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R8_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv0_2c32_R8_1_I1 /\ HandleRequestVoteResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,Inv11_f533_R10_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_2c32_R8_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_2c32_R8_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_2c32_R8_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_2c32_R8_1_I1
  \* (Inv0_2c32_R8_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_2c32_R8_1_I1 /\ HandleAppendEntriesResponseAction => Inv0_2c32_R8_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_2c32_R8_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_82b3_R12_1_I0
THEOREM L_12 == TypeOK /\ Inv13_3715_R22_0_I0 /\ Inv7_82b3_R12_1_I0 /\ Next => Inv7_82b3_R12_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_82b3_R12_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_82b3_R12_1_I0 /\ RequestVoteAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_82b3_R12_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_82b3_R12_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_82b3_R12_1_I0 /\ UpdateTermAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_82b3_R12_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_82b3_R12_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_82b3_R12_1_I0 /\ BecomeLeaderAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_82b3_R12_1_I0
  \* (Inv7_82b3_R12_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_82b3_R12_1_I0 /\ ClientRequestAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_82b3_R12_1_I0
  \* (Inv7_82b3_R12_1_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv7_82b3_R12_1_I0 /\ AppendEntriesAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_82b3_R12_1_I0
  \* (Inv7_82b3_R12_1_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_3715_R22_0_I0 /\ Inv7_82b3_R12_1_I0 /\ HandleRequestVoteRequestAction => Inv7_82b3_R12_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv13_3715_R22_0_I0,
                        Inv7_82b3_R12_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv7_82b3_R12_1_I0
    
    <2>1 CASE m.mterm # currentTerm[m.mdest]
          BY <2>1 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
          BY <2>2 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3, <3>1 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
            BY <2>3, <3>2 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
            BY <2>3, <3>3 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3, <3>4 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY  <4>1, <2>3,<3>4 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
              BY <2>3, <3>5 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
              BY <2>3, <3>5, <4>1 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>3. QED 
              BY <3>6 DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6    
    <2> QED
      BY DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_82b3_R12_1_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_82b3_R12_1_I0 /\ HandleRequestVoteResponseAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_82b3_R12_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_82b3_R12_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_82b3_R12_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_82b3_R12_1_I0
  \* (Inv7_82b3_R12_1_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_82b3_R12_1_I0 /\ HandleAppendEntriesResponseAction => Inv7_82b3_R12_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_82b3_R12_1_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv9_928b_R5_1_I2
THEOREM L_13 == TypeOK /\ Inv387_09bb_R9_0_I1 /\ Inv9_928b_R5_1_I2 /\ Next => Inv9_928b_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv9_928b_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_928b_R5_1_I2 /\ RequestVoteAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv9_928b_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_928b_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv9_928b_R5_1_I2 /\ UpdateTermAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv9_928b_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv9_928b_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv9_928b_R5_1_I2 /\ BecomeLeaderAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv9_928b_R5_1_I2
  \* (Inv9_928b_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv9_928b_R5_1_I2 /\ ClientRequestAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv9_928b_R5_1_I2
  \* (Inv9_928b_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv9_928b_R5_1_I2 /\ AppendEntriesAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv9_928b_R5_1_I2
  \* (Inv9_928b_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv9_928b_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv9_928b_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_928b_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv387_09bb_R9_0_I1 /\ Inv9_928b_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,Inv387_09bb_R9_0_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv9_928b_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv9_928b_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv9_928b_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv9_928b_R5_1_I2
  \* (Inv9_928b_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv9_928b_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv9_928b_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv9_928b_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv387_09bb_R9_0_I1
THEOREM L_14 == TypeOK /\ Inv81_fe26_R20_0_I1 /\ Inv387_09bb_R9_0_I1 /\ Next => Inv387_09bb_R9_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv387_09bb_R9_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv387_09bb_R9_0_I1 /\ RequestVoteAction => Inv387_09bb_R9_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv387_09bb_R9_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~(VARREQVRES.mdest = VARI) \/ (~(votesGranted[VARI] = {})))'
      BY DEF Inv387_09bb_R9_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv387_09bb_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv387_09bb_R9_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv387_09bb_R9_0_I1 /\ UpdateTermAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv387_09bb_R9_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv387_09bb_R9_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv387_09bb_R9_0_I1 /\ BecomeLeaderAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv387_09bb_R9_0_I1 /\ ClientRequestAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv387_09bb_R9_0_I1 /\ AppendEntriesAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv81_fe26_R20_0_I1 /\ Inv387_09bb_R9_0_I1 /\ HandleRequestVoteRequestAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,Inv81_fe26_R20_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv387_09bb_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv387_09bb_R9_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv387_09bb_R9_0_I1 /\ HandleRequestVoteResponseAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv387_09bb_R9_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv387_09bb_R9_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv387_09bb_R9_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv387_09bb_R9_0_I1
  \* (Inv387_09bb_R9_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv387_09bb_R9_0_I1 /\ HandleAppendEntriesResponseAction => Inv387_09bb_R9_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv387_09bb_R9_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv81_fe26_R20_0_I1
THEOREM L_15 == TypeOK /\ Inv81_fe26_R20_0_I1 /\ Next => Inv81_fe26_R20_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv81_fe26_R20_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv81_fe26_R20_0_I1 /\ RequestVoteAction => Inv81_fe26_R20_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv81_fe26_R20_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARREQVM \in requestVoteRequestMsgs',
                        (VARREQVM.msource = VARI)'
                 PROVE  (~(votesGranted[VARI] = {}))'
      BY DEF Inv81_fe26_R20_0_I1, RequestVoteAction
    <2>1 CASE i = VARI
          BY <2>1, SMTT(60), FS_Difference, FS_EmptySet, FS_Singleton DEF TypeOK,RequestVoteAction,RequestVote,Inv81_fe26_R20_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,LastTerm
    <2>2 CASE i # VARI
          BY <2>2, SMTT(60), FS_Difference, FS_EmptySet, FS_Singleton DEF TypeOK,RequestVoteAction,RequestVote,Inv81_fe26_R20_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,LastTerm
    
    <2> QED
      BY <2>1, <2>2, FS_Difference, FS_EmptySet, FS_Singleton DEF TypeOK,RequestVoteAction,RequestVote,Inv81_fe26_R20_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,LastTerm
    
  \* (Inv81_fe26_R20_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv81_fe26_R20_0_I1 /\ UpdateTermAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv81_fe26_R20_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv81_fe26_R20_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv81_fe26_R20_0_I1 /\ BecomeLeaderAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv81_fe26_R20_0_I1
  \* (Inv81_fe26_R20_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv81_fe26_R20_0_I1 /\ ClientRequestAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv81_fe26_R20_0_I1
  \* (Inv81_fe26_R20_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv81_fe26_R20_0_I1 /\ AppendEntriesAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv81_fe26_R20_0_I1
  \* (Inv81_fe26_R20_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv81_fe26_R20_0_I1 /\ HandleRequestVoteRequestAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv81_fe26_R20_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv81_fe26_R20_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv81_fe26_R20_0_I1 /\ HandleRequestVoteResponseAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv81_fe26_R20_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv81_fe26_R20_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv81_fe26_R20_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv81_fe26_R20_0_I1
  \* (Inv81_fe26_R20_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv81_fe26_R20_0_I1 /\ HandleAppendEntriesResponseAction => Inv81_fe26_R20_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv81_fe26_R20_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv1630_58c9_R5_1_I2
THEOREM L_16 == TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv13_6261_R6_1_I1 /\ Inv4_42ac_R5_1_I2 /\ Inv1630_58c9_R5_1_I2 /\ Next => Inv1630_58c9_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1630_58c9_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_2c32_R8_1_I1 /\ Inv1630_58c9_R5_1_I2 /\ RequestVoteAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,Inv0_2c32_R8_1_I1,RequestVoteAction,RequestVote,Inv1630_58c9_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1630_58c9_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ UpdateTermAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1630_58c9_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1630_58c9_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ BecomeLeaderAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1630_58c9_R5_1_I2
  \* (Inv1630_58c9_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ ClientRequestAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1630_58c9_R5_1_I2
  \* (Inv1630_58c9_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ AppendEntriesAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1630_58c9_R5_1_I2
  \* (Inv1630_58c9_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1630_58c9_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1630_58c9_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv13_6261_R6_1_I1 /\ Inv4_42ac_R5_1_I2 /\ Inv1630_58c9_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,Inv11_f533_R10_0_I0,Inv13_6261_R6_1_I1,Inv4_42ac_R5_1_I2,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1630_58c9_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1630_58c9_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1630_58c9_R5_1_I2
  \* (Inv1630_58c9_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv1630_58c9_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv1630_58c9_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1630_58c9_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv13_6261_R6_1_I1
THEOREM L_17 == TypeOK /\ Inv13_6261_R6_1_I1 /\ Next => Inv13_6261_R6_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv13_6261_R6_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv13_6261_R6_1_I1 /\ RequestVoteAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv13_6261_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_6261_R6_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv13_6261_R6_1_I1 /\ UpdateTermAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv13_6261_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv13_6261_R6_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv13_6261_R6_1_I1 /\ BecomeLeaderAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv13_6261_R6_1_I1
  \* (Inv13_6261_R6_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv13_6261_R6_1_I1 /\ ClientRequestAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv13_6261_R6_1_I1
  \* (Inv13_6261_R6_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv13_6261_R6_1_I1 /\ AppendEntriesAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv13_6261_R6_1_I1
  \* (Inv13_6261_R6_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv13_6261_R6_1_I1 /\ HandleRequestVoteRequestAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv13_6261_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_6261_R6_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_6261_R6_1_I1 /\ HandleRequestVoteResponseAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv13_6261_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv13_6261_R6_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv13_6261_R6_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv13_6261_R6_1_I1
  \* (Inv13_6261_R6_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv13_6261_R6_1_I1 /\ HandleAppendEntriesResponseAction => Inv13_6261_R6_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv13_6261_R6_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5771_fffd_R5_1_I2
THEOREM L_18 == TypeOK /\ Inv5771_fffd_R5_1_I2 /\ Next => Inv5771_fffd_R5_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5771_fffd_R5_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ RequestVoteAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5771_fffd_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5771_fffd_R5_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ UpdateTermAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5771_fffd_R5_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5771_fffd_R5_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ BecomeLeaderAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5771_fffd_R5_1_I2
  \* (Inv5771_fffd_R5_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ ClientRequestAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5771_fffd_R5_1_I2
  \* (Inv5771_fffd_R5_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ AppendEntriesAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5771_fffd_R5_1_I2
  \* (Inv5771_fffd_R5_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ HandleRequestVoteRequestAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5771_fffd_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5771_fffd_R5_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ HandleRequestVoteResponseAction => Inv5771_fffd_R5_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv5771_fffd_R5_1_I2,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~((state[VARJ] = Leader))) \/ ((votesGranted[VARJ] \in Quorum)))'
      BY DEF HandleRequestVoteResponseAction, Inv5771_fffd_R5_1_I2
    <2> QED
      BY AddingToQuorumRemainsQuorum DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5771_fffd_R5_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5771_fffd_R5_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5771_fffd_R5_1_I2
  \* (Inv5771_fffd_R5_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5771_fffd_R5_1_I2 /\ HandleAppendEntriesResponseAction => Inv5771_fffd_R5_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5771_fffd_R5_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv8096_c721_R2_2_I2
THEOREM L_19 == TypeOK /\ Inv7_1e2e_R6_3_I1 /\ Inv6746_404d_R2_1_I2 /\ Inv13_6261_R6_1_I1 /\ Inv4_42ac_R5_1_I2 /\ Inv138_3acc_R6_1_I1 /\ Inv2_8e53_R5_0_I0 /\ Inv5_c57a_R6_2_I1 /\ Inv13_6261_R6_1_I1 /\ Inv607_376d_R6_2_I1 /\ Inv6390_7e0d_R1_1_I2 /\ Inv8096_c721_R2_2_I2 /\ Next => Inv8096_c721_R2_2_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet, RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType, CanAppend, LogOk
  \* (Inv8096_c721_R2_2_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ Inv8096_c721_R2_2_I2 /\ RequestVoteAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,Inv7_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv8096_c721_R2_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8096_c721_R2_2_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv8096_c721_R2_2_I2 /\ UpdateTermAction => Inv8096_c721_R2_2_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8096_c721_R2_2_I2,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m.mterm, m.mdest),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)))'
      BY DEF Inv8096_c721_R2_2_I2, UpdateTermAction
    <2> QED
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8096_c721_R2_2_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8096_c721_R2_2_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8096_c721_R2_2_I2 /\ BecomeLeaderAction => Inv8096_c721_R2_2_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8096_c721_R2_2_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (~((state[VARI] = Candidate)) \/ (~(\E INDK \in DOMAIN log[VARJ] : log[VARJ][INDK] = currentTerm[VARI])) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs)))'
      BY DEF BecomeLeaderAction, Inv8096_c721_R2_2_I2
    <2> QED
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv8096_c721_R2_2_I2
  \* (Inv8096_c721_R2_2_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6746_404d_R2_1_I2 /\ Inv13_6261_R6_1_I1 /\ Inv4_42ac_R5_1_I2 /\ Inv138_3acc_R6_1_I1 /\ Inv2_8e53_R5_0_I0 /\ Inv8096_c721_R2_2_I2 /\ ClientRequestAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,Inv6746_404d_R2_1_I2,Inv13_6261_R6_1_I1,Inv4_42ac_R5_1_I2,Inv138_3acc_R6_1_I1,Inv2_8e53_R5_0_I0,ClientRequestAction,ClientRequest,Inv8096_c721_R2_2_I2
  \* (Inv8096_c721_R2_2_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv8096_c721_R2_2_I2 /\ AppendEntriesAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8096_c721_R2_2_I2
  \* (Inv8096_c721_R2_2_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_c57a_R6_2_I1 /\ Inv13_6261_R6_1_I1 /\ Inv607_376d_R6_2_I1 /\ Inv8096_c721_R2_2_I2 /\ HandleRequestVoteRequestAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,Inv5_c57a_R6_2_I1,Inv13_6261_R6_1_I1,Inv607_376d_R6_2_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8096_c721_R2_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8096_c721_R2_2_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv8096_c721_R2_2_I2 /\ HandleRequestVoteResponseAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8096_c721_R2_2_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8096_c721_R2_2_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6390_7e0d_R1_1_I2 /\ Inv8096_c721_R2_2_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,Inv6390_7e0d_R1_1_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8096_c721_R2_2_I2
  \* (Inv8096_c721_R2_2_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv8096_c721_R2_2_I2 /\ HandleAppendEntriesResponseAction => Inv8096_c721_R2_2_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8096_c721_R2_2_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv138_3acc_R6_1_I1
THEOREM L_20 == TypeOK /\ Inv138_3acc_R6_1_I1 /\ Next => Inv138_3acc_R6_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv138_3acc_R6_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv138_3acc_R6_1_I1 /\ RequestVoteAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv138_3acc_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv138_3acc_R6_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv138_3acc_R6_1_I1 /\ UpdateTermAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv138_3acc_R6_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv138_3acc_R6_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv138_3acc_R6_1_I1 /\ BecomeLeaderAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv138_3acc_R6_1_I1
  \* (Inv138_3acc_R6_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv138_3acc_R6_1_I1 /\ ClientRequestAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv138_3acc_R6_1_I1
  \* (Inv138_3acc_R6_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv138_3acc_R6_1_I1 /\ AppendEntriesAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv138_3acc_R6_1_I1
  \* (Inv138_3acc_R6_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv138_3acc_R6_1_I1 /\ HandleRequestVoteRequestAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv138_3acc_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv138_3acc_R6_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv138_3acc_R6_1_I1 /\ HandleRequestVoteResponseAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv138_3acc_R6_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv138_3acc_R6_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv138_3acc_R6_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv138_3acc_R6_1_I1
  \* (Inv138_3acc_R6_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv138_3acc_R6_1_I1 /\ HandleAppendEntriesResponseAction => Inv138_3acc_R6_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv138_3acc_R6_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_c57a_R6_2_I1
THEOREM L_21 == TypeOK /\ Inv31_73fd_R15_1_I1  /\ Inv138_3acc_R6_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv11_dadc_R15_1_I1 /\ Inv31_73fd_R15_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv107_791e_R15_2_I1 /\ Inv7_2014_R15_0_I1 /\ Inv8509_2dd8_R0_0_I2 /\ Inv5_c57a_R6_2_I1 /\ Next => Inv5_c57a_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_LogEntryInTermImpliesSafeAtTerm
  \* (Inv5_c57a_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_c57a_R6_2_I1 /\ RequestVoteAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_c57a_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_c57a_R6_2_I1 /\ UpdateTermAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_c57a_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_c57a_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5_c57a_R6_2_I1 /\ BecomeLeaderAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5_c57a_R6_2_I1
  \* (Inv5_c57a_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv138_3acc_R6_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv11_dadc_R15_1_I1 /\ Inv5_c57a_R6_2_I1 /\ ClientRequestAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,Inv31_73fd_R15_1_I1,Inv138_3acc_R6_1_I1,Inv0_2c32_R8_1_I1,Inv11_dadc_R15_1_I1,ClientRequestAction,ClientRequest,Inv5_c57a_R6_2_I1
  \* (Inv5_c57a_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_c57a_R6_2_I1 /\ AppendEntriesAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_c57a_R6_2_I1
  \* (Inv5_c57a_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_c57a_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_c57a_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv107_791e_R15_2_I1 /\ Inv5_c57a_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,Inv31_73fd_R15_1_I1,Inv11_f533_R10_0_I0,Inv107_791e_R15_2_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_c57a_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_c57a_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_2014_R15_0_I1 /\ Inv8509_2dd8_R0_0_I2 /\ Inv5_c57a_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,Inv7_2014_R15_0_I1,Inv8509_2dd8_R0_0_I2,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_c57a_R6_2_I1
  \* (Inv5_c57a_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_c57a_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv5_c57a_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_c57a_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_2014_R15_0_I1
THEOREM L_22 == TypeOK /\ Inv12_0a54_R24_0_I1 /\ Inv379_f624_R24_0_I1 /\ Inv18_bf9f_R24_0_I1 /\ Inv7_2014_R15_0_I1 /\ Next => Inv7_2014_R15_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_LogEntryInTermImpliesSafeAtTermAppendEntries
  \* (Inv7_2014_R15_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_2014_R15_0_I1 /\ RequestVoteAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_2014_R15_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_2014_R15_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_2014_R15_0_I1 /\ UpdateTermAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_2014_R15_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_2014_R15_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_2014_R15_0_I1 /\ BecomeLeaderAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_2014_R15_0_I1
  \* (Inv7_2014_R15_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_2014_R15_0_I1 /\ ClientRequestAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_2014_R15_0_I1
  \* (Inv7_2014_R15_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv12_0a54_R24_0_I1 /\ Inv379_f624_R24_0_I1 /\ Inv18_bf9f_R24_0_I1 /\ Inv7_2014_R15_0_I1 /\ AppendEntriesAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,Inv12_0a54_R24_0_I1,Inv379_f624_R24_0_I1,Inv18_bf9f_R24_0_I1,AppendEntriesAction,AppendEntries,Inv7_2014_R15_0_I1
  \* (Inv7_2014_R15_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv7_2014_R15_0_I1 /\ HandleRequestVoteRequestAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_2014_R15_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_2014_R15_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_2014_R15_0_I1 /\ HandleRequestVoteResponseAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_2014_R15_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_2014_R15_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_2014_R15_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_2014_R15_0_I1
  \* (Inv7_2014_R15_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_2014_R15_0_I1 /\ HandleAppendEntriesResponseAction => Inv7_2014_R15_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_2014_R15_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv12_0a54_R24_0_I1
THEOREM L_23 == TypeOK /\ Inv12_0a54_R24_0_I1 /\ Next => Inv12_0a54_R24_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv12_0a54_R24_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv12_0a54_R24_0_I1 /\ RequestVoteAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv12_0a54_R24_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_0a54_R24_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv12_0a54_R24_0_I1 /\ UpdateTermAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv12_0a54_R24_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv12_0a54_R24_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv12_0a54_R24_0_I1 /\ BecomeLeaderAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv12_0a54_R24_0_I1
  \* (Inv12_0a54_R24_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv12_0a54_R24_0_I1 /\ ClientRequestAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv12_0a54_R24_0_I1
  \* (Inv12_0a54_R24_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv12_0a54_R24_0_I1 /\ AppendEntriesAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv12_0a54_R24_0_I1
  \* (Inv12_0a54_R24_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv12_0a54_R24_0_I1 /\ HandleRequestVoteRequestAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv12_0a54_R24_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_0a54_R24_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv12_0a54_R24_0_I1 /\ HandleRequestVoteResponseAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv12_0a54_R24_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv12_0a54_R24_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv12_0a54_R24_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv12_0a54_R24_0_I1
  \* (Inv12_0a54_R24_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv12_0a54_R24_0_I1 /\ HandleAppendEntriesResponseAction => Inv12_0a54_R24_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv12_0a54_R24_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv379_f624_R24_0_I1
THEOREM L_24 == TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv10303_8d53_R26_3_I2 /\ Inv11_dadc_R15_1_I1 /\ Inv379_f624_R24_0_I1 /\ Next => Inv379_f624_R24_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_QuorumsSafeAtTerms
  \* (Inv379_f624_R24_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv379_f624_R24_0_I1 /\ RequestVoteAction => Inv379_f624_R24_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv379_f624_R24_0_I1,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server'
                 PROVE  ((H_QuorumsSafeAtTerms /\ currentTerm = currentTerm /\ state = state /\ votedFor = votedFor) \/ (~((state[VARI] = Leader))))'
      BY DEF Inv379_f624_R24_0_I1, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv379_f624_R24_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv379_f624_R24_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv379_f624_R24_0_I1 /\ UpdateTermAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv379_f624_R24_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv379_f624_R24_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv10303_8d53_R26_3_I2 /\ Inv11_dadc_R15_1_I1 /\ Inv379_f624_R24_0_I1 /\ BecomeLeaderAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,Inv31_73fd_R15_1_I1,Inv10303_8d53_R26_3_I2,Inv11_dadc_R15_1_I1,BecomeLeaderAction,BecomeLeader,Inv379_f624_R24_0_I1
  \* (Inv379_f624_R24_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv379_f624_R24_0_I1 /\ ClientRequestAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv379_f624_R24_0_I1
  \* (Inv379_f624_R24_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv379_f624_R24_0_I1 /\ AppendEntriesAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv379_f624_R24_0_I1
  \* (Inv379_f624_R24_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv379_f624_R24_0_I1 /\ HandleRequestVoteRequestAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv379_f624_R24_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv379_f624_R24_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv379_f624_R24_0_I1 /\ HandleRequestVoteResponseAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv379_f624_R24_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv379_f624_R24_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv379_f624_R24_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv379_f624_R24_0_I1
  \* (Inv379_f624_R24_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv379_f624_R24_0_I1 /\ HandleAppendEntriesResponseAction => Inv379_f624_R24_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv379_f624_R24_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv31_73fd_R15_1_I1
THEOREM L_25 == TypeOK /\ Inv31_73fd_R15_1_I1 /\ Next => Inv31_73fd_R15_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv31_73fd_R15_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv31_73fd_R15_1_I1 /\ RequestVoteAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv31_73fd_R15_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_73fd_R15_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv31_73fd_R15_1_I1 /\ UpdateTermAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv31_73fd_R15_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv31_73fd_R15_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv31_73fd_R15_1_I1 /\ BecomeLeaderAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv31_73fd_R15_1_I1
  \* (Inv31_73fd_R15_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv31_73fd_R15_1_I1 /\ ClientRequestAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv31_73fd_R15_1_I1
  \* (Inv31_73fd_R15_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv31_73fd_R15_1_I1 /\ AppendEntriesAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv31_73fd_R15_1_I1
  \* (Inv31_73fd_R15_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv31_73fd_R15_1_I1 /\ HandleRequestVoteRequestAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv31_73fd_R15_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_73fd_R15_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv31_73fd_R15_1_I1 /\ HandleRequestVoteResponseAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv31_73fd_R15_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv31_73fd_R15_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv31_73fd_R15_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv31_73fd_R15_1_I1
  \* (Inv31_73fd_R15_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv31_73fd_R15_1_I1 /\ HandleAppendEntriesResponseAction => Inv31_73fd_R15_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv31_73fd_R15_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv10303_8d53_R26_3_I2
THEOREM L_26 == TypeOK /\ Inv17_e2fa_R26_0_I1 /\ Inv11_f533_R10_0_I0 /\ Inv10303_8d53_R26_3_I2 /\ Next => Inv10303_8d53_R26_3_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10303_8d53_R26_3_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ RequestVoteAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10303_8d53_R26_3_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10303_8d53_R26_3_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ UpdateTermAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10303_8d53_R26_3_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10303_8d53_R26_3_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ BecomeLeaderAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10303_8d53_R26_3_I2
  \* (Inv10303_8d53_R26_3_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ ClientRequestAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10303_8d53_R26_3_I2
  \* (Inv10303_8d53_R26_3_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ AppendEntriesAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10303_8d53_R26_3_I2
  \* (Inv10303_8d53_R26_3_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ Inv10303_8d53_R26_3_I2 /\ HandleRequestVoteRequestAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,Inv17_e2fa_R26_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10303_8d53_R26_3_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10303_8d53_R26_3_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv11_f533_R10_0_I0 /\ Inv10303_8d53_R26_3_I2 /\ HandleRequestVoteResponseAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,Inv11_f533_R10_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10303_8d53_R26_3_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10303_8d53_R26_3_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10303_8d53_R26_3_I2
  \* (Inv10303_8d53_R26_3_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ HandleAppendEntriesResponseAction => Inv10303_8d53_R26_3_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10303_8d53_R26_3_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv17_e2fa_R26_0_I1
THEOREM L_27 == TypeOK /\ Inv17_e2fa_R26_0_I1 /\ Next => Inv17_e2fa_R26_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv17_e2fa_R26_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ RequestVoteAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv17_e2fa_R26_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17_e2fa_R26_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ UpdateTermAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv17_e2fa_R26_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv17_e2fa_R26_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ BecomeLeaderAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv17_e2fa_R26_0_I1
  \* (Inv17_e2fa_R26_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ ClientRequestAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv17_e2fa_R26_0_I1
  \* (Inv17_e2fa_R26_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ AppendEntriesAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv17_e2fa_R26_0_I1
  \* (Inv17_e2fa_R26_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ HandleRequestVoteRequestAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv17_e2fa_R26_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17_e2fa_R26_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ HandleRequestVoteResponseAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv17_e2fa_R26_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv17_e2fa_R26_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv17_e2fa_R26_0_I1
  \* (Inv17_e2fa_R26_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ HandleAppendEntriesResponseAction => Inv17_e2fa_R26_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv17_e2fa_R26_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv11_dadc_R15_1_I1
THEOREM L_28 == TypeOK /\ Inv9_928b_R5_1_I2 /\ Inv31_73fd_R15_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv21_3b9d_R26_2_I1 /\ Inv10303_8d53_R26_3_I2 /\ Inv17_e2fa_R26_0_I1 /\ Inv13_3715_R22_0_I0 /\ Inv11_dadc_R15_1_I1 /\ Next => Inv11_dadc_R15_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv11_dadc_R15_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv9_928b_R5_1_I2 /\ Inv31_73fd_R15_1_I1 /\ Inv0_2c32_R8_1_I1 /\ Inv21_3b9d_R26_2_I1 /\ Inv11_dadc_R15_1_I1 /\ RequestVoteAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,Inv9_928b_R5_1_I2,Inv31_73fd_R15_1_I1,Inv0_2c32_R8_1_I1,Inv21_3b9d_R26_2_I1,RequestVoteAction,RequestVote,Inv11_dadc_R15_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_dadc_R15_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10303_8d53_R26_3_I2 /\ Inv11_dadc_R15_1_I1 /\ UpdateTermAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,Inv10303_8d53_R26_3_I2,UpdateTermAction,UpdateTerm,Inv11_dadc_R15_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv11_dadc_R15_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv11_dadc_R15_1_I1 /\ BecomeLeaderAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv11_dadc_R15_1_I1
  \* (Inv11_dadc_R15_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv11_dadc_R15_1_I1 /\ ClientRequestAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv11_dadc_R15_1_I1
  \* (Inv11_dadc_R15_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv11_dadc_R15_1_I1 /\ AppendEntriesAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv11_dadc_R15_1_I1
  \* (Inv11_dadc_R15_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ Inv11_dadc_R15_1_I1 /\ HandleRequestVoteRequestAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,Inv17_e2fa_R26_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv11_dadc_R15_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv11_dadc_R15_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv13_3715_R22_0_I0 /\ Inv11_dadc_R15_1_I1 /\ HandleRequestVoteResponseAction => Inv11_dadc_R15_1_I1' 
    <2> SUFFICES ASSUME TypeOK /\ Inv13_3715_R22_0_I0 /\ Inv11_dadc_R15_1_I1 /\ HandleRequestVoteResponseAction,
                        NEW VARI \in Server',
                        (votedFor[VARI] = VARI)',
                        NEW t \in (votesGranted[VARI])'
                 PROVE  (/\ currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
      BY DEF Inv11_dadc_R15_1_I1
    <2>1. (currentTerm[t] = currentTerm[VARI] => votedFor[t] = VARI)'
      <3> SUFFICES ASSUME NEW m \in requestVoteResponseMsgs,
                          HandleRequestVoteResponse(m),
                          (currentTerm[t] = currentTerm[VARI])'
                   PROVE  (votedFor[t] = VARI)'
        BY DEF HandleRequestVoteResponseAction
      <3> QED
        BY DEF TypeOK,Inv13_3715_R22_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv11_dadc_R15_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
    <2>2. QED
      BY <2>1
    
  \* (Inv11_dadc_R15_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv11_dadc_R15_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv11_dadc_R15_1_I1
  \* (Inv11_dadc_R15_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv11_dadc_R15_1_I1 /\ HandleAppendEntriesResponseAction => Inv11_dadc_R15_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv11_dadc_R15_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv21_3b9d_R26_2_I1
THEOREM L_29 == TypeOK /\ Inv17_e2fa_R26_0_I1 /\ Inv21_3b9d_R26_2_I1 /\ Next => Inv21_3b9d_R26_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv21_3b9d_R26_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ RequestVoteAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv21_3b9d_R26_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21_3b9d_R26_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ UpdateTermAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv21_3b9d_R26_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv21_3b9d_R26_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ BecomeLeaderAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv21_3b9d_R26_2_I1
  \* (Inv21_3b9d_R26_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ ClientRequestAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv21_3b9d_R26_2_I1
  \* (Inv21_3b9d_R26_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ AppendEntriesAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv21_3b9d_R26_2_I1
  \* (Inv21_3b9d_R26_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv17_e2fa_R26_0_I1 /\ Inv21_3b9d_R26_2_I1 /\ HandleRequestVoteRequestAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,Inv17_e2fa_R26_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv21_3b9d_R26_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21_3b9d_R26_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ HandleRequestVoteResponseAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv21_3b9d_R26_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv21_3b9d_R26_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv21_3b9d_R26_2_I1
  \* (Inv21_3b9d_R26_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv21_3b9d_R26_2_I1 /\ HandleAppendEntriesResponseAction => Inv21_3b9d_R26_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv21_3b9d_R26_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv18_bf9f_R24_0_I1
THEOREM L_30 == TypeOK /\ Inv6_9fea_R34_0_I1 /\ Inv18_bf9f_R24_0_I1 /\ Next => Inv18_bf9f_R24_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv18_bf9f_R24_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ RequestVoteAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv18_bf9f_R24_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_bf9f_R24_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ UpdateTermAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv18_bf9f_R24_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv18_bf9f_R24_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ BecomeLeaderAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv18_bf9f_R24_0_I1
  \* (Inv18_bf9f_R24_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ ClientRequestAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv18_bf9f_R24_0_I1
  \* (Inv18_bf9f_R24_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ AppendEntriesAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv18_bf9f_R24_0_I1
  \* (Inv18_bf9f_R24_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ HandleRequestVoteRequestAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv18_bf9f_R24_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_bf9f_R24_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ HandleRequestVoteResponseAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv18_bf9f_R24_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv18_bf9f_R24_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_9fea_R34_0_I1 /\ Inv18_bf9f_R24_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,Inv6_9fea_R34_0_I1,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv18_bf9f_R24_0_I1
  \* (Inv18_bf9f_R24_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ HandleAppendEntriesResponseAction => Inv18_bf9f_R24_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv18_bf9f_R24_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv6_9fea_R34_0_I1
THEOREM L_31 == TypeOK /\ Inv18_bf9f_R24_0_I1 /\ Inv6_9fea_R34_0_I1 /\ Next => Inv6_9fea_R34_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_9fea_R34_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_9fea_R34_0_I1 /\ RequestVoteAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_9fea_R34_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_9fea_R34_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_9fea_R34_0_I1 /\ UpdateTermAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_9fea_R34_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_9fea_R34_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_9fea_R34_0_I1 /\ BecomeLeaderAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_9fea_R34_0_I1
  \* (Inv6_9fea_R34_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_9fea_R34_0_I1 /\ ClientRequestAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_9fea_R34_0_I1
  \* (Inv6_9fea_R34_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ Inv6_9fea_R34_0_I1 /\ AppendEntriesAction => Inv6_9fea_R34_0_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv18_bf9f_R24_0_I1,
                        Inv6_9fea_R34_0_I1,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  ((VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] <= VARMAEREQ.mterm) \/ ((VARMAEREQ.mentries = <<>>)))'
      BY DEF AppendEntriesAction, Inv6_9fea_R34_0_I1
    <2> QED
      BY DEF TypeOK,Inv18_bf9f_R24_0_I1,AppendEntriesAction,AppendEntries,Inv6_9fea_R34_0_I1, Min
  \* (Inv6_9fea_R34_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv6_9fea_R34_0_I1 /\ HandleRequestVoteRequestAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_9fea_R34_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_9fea_R34_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv6_9fea_R34_0_I1 /\ HandleRequestVoteResponseAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_9fea_R34_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_9fea_R34_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv6_9fea_R34_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_9fea_R34_0_I1
  \* (Inv6_9fea_R34_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv6_9fea_R34_0_I1 /\ HandleAppendEntriesResponseAction => Inv6_9fea_R34_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_9fea_R34_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv107_791e_R15_2_I1
THEOREM L_32 == TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv0_5020_R27_1_I1 /\ Inv0_5020_R27_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv18_bf9f_R24_0_I1 /\ Inv11_f533_R10_0_I0 /\ Inv13_3715_R22_0_I0 /\ Inv3_9e78_R17_0_I0 /\ Inv107_791e_R15_2_I1 /\ Next => Inv107_791e_R15_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv107_791e_R15_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv0_5020_R27_1_I1 /\ Inv107_791e_R15_2_I1 /\ RequestVoteAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,Inv31_73fd_R15_1_I1,Inv11_f533_R10_0_I0,Inv0_5020_R27_1_I1,RequestVoteAction,RequestVote,Inv107_791e_R15_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv107_791e_R15_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_5020_R27_1_I1 /\ Inv11_f533_R10_0_I0 /\ Inv107_791e_R15_2_I1 /\ UpdateTermAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,Inv0_5020_R27_1_I1,Inv11_f533_R10_0_I0,UpdateTermAction,UpdateTerm,Inv107_791e_R15_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv107_791e_R15_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv107_791e_R15_2_I1 /\ BecomeLeaderAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv107_791e_R15_2_I1
  \* (Inv107_791e_R15_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv107_791e_R15_2_I1 /\ ClientRequestAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv107_791e_R15_2_I1
  \* (Inv107_791e_R15_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv107_791e_R15_2_I1 /\ AppendEntriesAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv107_791e_R15_2_I1
  \* (Inv107_791e_R15_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv18_bf9f_R24_0_I1 /\ Inv11_f533_R10_0_I0 /\ Inv13_3715_R22_0_I0 /\ Inv3_9e78_R17_0_I0 /\ Inv107_791e_R15_2_I1 /\ HandleRequestVoteRequestAction => Inv107_791e_R15_2_I1' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv18_bf9f_R24_0_I1,
                        Inv11_f533_R10_0_I0,
                        Inv13_3715_R22_0_I0,
                        Inv3_9e78_R17_0_I0,
                        Inv107_791e_R15_2_I1,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARREQVRES \in requestVoteResponseMsgs'
                 PROVE  (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted) \/ (~(votedFor[VARJ] = VARI)))'
      BY DEF HandleRequestVoteRequestAction, Inv107_791e_R15_2_I1
    <2> QED
      BY DEF TypeOK,Inv18_bf9f_R24_0_I1,Inv11_f533_R10_0_I0,Inv13_3715_R22_0_I0,Inv3_9e78_R17_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv107_791e_R15_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv107_791e_R15_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv107_791e_R15_2_I1 /\ HandleRequestVoteResponseAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv107_791e_R15_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv107_791e_R15_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv107_791e_R15_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv107_791e_R15_2_I1
  \* (Inv107_791e_R15_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv107_791e_R15_2_I1 /\ HandleAppendEntriesResponseAction => Inv107_791e_R15_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv107_791e_R15_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv3_9e78_R17_0_I0
THEOREM L_33 == TypeOK /\ Inv3_9e78_R17_0_I0 /\ Next => Inv3_9e78_R17_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_9e78_R17_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_9e78_R17_0_I0 /\ RequestVoteAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_9e78_R17_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_9e78_R17_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_9e78_R17_0_I0 /\ UpdateTermAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_9e78_R17_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_9e78_R17_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_9e78_R17_0_I0 /\ BecomeLeaderAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_9e78_R17_0_I0
  \* (Inv3_9e78_R17_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_9e78_R17_0_I0 /\ ClientRequestAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_9e78_R17_0_I0
  \* (Inv3_9e78_R17_0_I0,AppendEntriesAction)
  <1>5. TypeOK /\ Inv3_9e78_R17_0_I0 /\ AppendEntriesAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_9e78_R17_0_I0
  \* (Inv3_9e78_R17_0_I0,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_9e78_R17_0_I0 /\ HandleRequestVoteRequestAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_9e78_R17_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_9e78_R17_0_I0,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv3_9e78_R17_0_I0 /\ HandleRequestVoteResponseAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_9e78_R17_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_9e78_R17_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv3_9e78_R17_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_9e78_R17_0_I0
  \* (Inv3_9e78_R17_0_I0,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv3_9e78_R17_0_I0 /\ HandleAppendEntriesResponseAction => Inv3_9e78_R17_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_9e78_R17_0_I0
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv0_5020_R27_1_I1
THEOREM L_34 == TypeOK /\ Inv3_9e78_R17_0_I0 /\ Inv0_5020_R27_1_I1 /\ Next => Inv0_5020_R27_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_5020_R27_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_5020_R27_1_I1 /\ RequestVoteAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_5020_R27_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_5020_R27_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_5020_R27_1_I1 /\ UpdateTermAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_5020_R27_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_5020_R27_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_5020_R27_1_I1 /\ BecomeLeaderAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_5020_R27_1_I1
  \* (Inv0_5020_R27_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_5020_R27_1_I1 /\ ClientRequestAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_5020_R27_1_I1
  \* (Inv0_5020_R27_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv0_5020_R27_1_I1 /\ AppendEntriesAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_5020_R27_1_I1
  \* (Inv0_5020_R27_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_9e78_R17_0_I0 /\ Inv0_5020_R27_1_I1 /\ HandleRequestVoteRequestAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,Inv3_9e78_R17_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_5020_R27_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_5020_R27_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv0_5020_R27_1_I1 /\ HandleRequestVoteResponseAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_5020_R27_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_5020_R27_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv0_5020_R27_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_5020_R27_1_I1
  \* (Inv0_5020_R27_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv0_5020_R27_1_I1 /\ HandleAppendEntriesResponseAction => Inv0_5020_R27_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_5020_R27_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv607_376d_R6_2_I1
THEOREM L_35 == TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv607_376d_R6_2_I1 /\ Next => Inv607_376d_R6_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv607_376d_R6_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv607_376d_R6_2_I1 /\ RequestVoteAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv607_376d_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv607_376d_R6_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv607_376d_R6_2_I1 /\ UpdateTermAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv607_376d_R6_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv607_376d_R6_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv607_376d_R6_2_I1 /\ BecomeLeaderAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv607_376d_R6_2_I1
  \* (Inv607_376d_R6_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv607_376d_R6_2_I1 /\ ClientRequestAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv607_376d_R6_2_I1
  \* (Inv607_376d_R6_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv607_376d_R6_2_I1 /\ AppendEntriesAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv607_376d_R6_2_I1
  \* (Inv607_376d_R6_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv31_73fd_R15_1_I1 /\ Inv607_376d_R6_2_I1 /\ HandleRequestVoteRequestAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,Inv31_73fd_R15_1_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv607_376d_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv607_376d_R6_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv607_376d_R6_2_I1 /\ HandleRequestVoteResponseAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv607_376d_R6_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv607_376d_R6_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv607_376d_R6_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv607_376d_R6_2_I1
  \* (Inv607_376d_R6_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv607_376d_R6_2_I1 /\ HandleAppendEntriesResponseAction => Inv607_376d_R6_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv607_376d_R6_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7_1e2e_R6_3_I1
THEOREM L_36 == TypeOK /\ Inv3_9e78_R17_0_I0 /\ Inv7_1e2e_R6_3_I1 /\ Next => Inv7_1e2e_R6_3_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_1e2e_R6_3_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ RequestVoteAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv7_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_1e2e_R6_3_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ UpdateTermAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7_1e2e_R6_3_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_1e2e_R6_3_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ BecomeLeaderAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_1e2e_R6_3_I1
  \* (Inv7_1e2e_R6_3_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ ClientRequestAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_1e2e_R6_3_I1
  \* (Inv7_1e2e_R6_3_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ AppendEntriesAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_1e2e_R6_3_I1
  \* (Inv7_1e2e_R6_3_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv3_9e78_R17_0_I0 /\ Inv7_1e2e_R6_3_I1 /\ HandleRequestVoteRequestAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,Inv3_9e78_R17_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_1e2e_R6_3_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ HandleRequestVoteResponseAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_1e2e_R6_3_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_1e2e_R6_3_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_1e2e_R6_3_I1
  \* (Inv7_1e2e_R6_3_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ HandleAppendEntriesResponseAction => Inv7_1e2e_R6_3_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_1e2e_R6_3_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv7767_5b71_R4_1_I2
THEOREM L_37 == TypeOK /\ Inv7_1e2e_R6_3_I1 /\ Inv8096_c721_R2_2_I2 /\ Inv84_4aa6_R7_1_I1 /\ Inv5_c57a_R6_2_I1 /\ Inv9_928b_R5_1_I2 /\ Inv607_376d_R6_2_I1 /\ Safety /\ Inv7767_5b71_R4_1_I2 /\ Next => Inv7767_5b71_R4_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF GrantedVoteSet, Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,RequestVoteRequestType,RequestVoteResponseType,H_PrimaryHasEntriesItCreated
  \* (Inv7767_5b71_R4_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv7_1e2e_R6_3_I1 /\ Inv7767_5b71_R4_1_I2 /\ RequestVoteAction => Inv7767_5b71_R4_1_I2' BY DEF TypeOK,Inv7_1e2e_R6_3_I1,RequestVoteAction,RequestVote,Inv7767_5b71_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7767_5b71_R4_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ UpdateTermAction => Inv7767_5b71_R4_1_I2' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv7767_5b71_R4_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7767_5b71_R4_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ BecomeLeaderAction => Inv7767_5b71_R4_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv7767_5b71_R4_1_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]))))'
      BY DEF BecomeLeaderAction, Inv7767_5b71_R4_1_I2
    <2> QED
      BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7767_5b71_R4_1_I2
  \* (Inv7767_5b71_R4_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ ClientRequestAction => Inv7767_5b71_R4_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv7767_5b71_R4_1_I2,
                        TRUE,
                        NEW i \in Server,
                        ClientRequest(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]))))'
      BY DEF ClientRequestAction, Inv7767_5b71_R4_1_I2
    <2> QED
      BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7767_5b71_R4_1_I2
  \* (Inv7767_5b71_R4_1_I2,AppendEntriesAction)
  <1>5. TypeOK /\ Inv8096_c721_R2_2_I2 /\ Inv7767_5b71_R4_1_I2 /\ AppendEntriesAction => Inv7767_5b71_R4_1_I2' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv8096_c721_R2_2_I2,
                        Inv7767_5b71_R4_1_I2,
                        TRUE,
                        NEW i \in Server, NEW j \in Server,
                        AppendEntries(i, j),
                        NEW VARI \in Server',
                        NEW VARJ \in Server',
                        NEW VARMAEREQ \in appendEntriesRequestMsgs'
                 PROVE  (~((state[VARI] = Candidate /\ VARI # VARJ)) \/ (~(GrantedVoteSet(VARI) \in Quorum /\ votesGranted = votesGranted /\ requestVoteResponseMsgs = requestVoteResponseMsgs) \/ (~(VARMAEREQ.mentries # <<>> /\ VARMAEREQ.mentries[1] = currentTerm[VARI]))))'
      BY DEF AppendEntriesAction, Inv7767_5b71_R4_1_I2
    <2> QED
      BY DEF TypeOK,Inv8096_c721_R2_2_I2,AppendEntriesAction,AppendEntries,Inv7767_5b71_R4_1_I2
  \* (Inv7767_5b71_R4_1_I2,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ Inv5_c57a_R6_2_I1 /\ Inv9_928b_R5_1_I2 /\ Inv607_376d_R6_2_I1 /\ Safety /\ Inv7767_5b71_R4_1_I2 /\ HandleRequestVoteRequestAction => Inv7767_5b71_R4_1_I2' BY DEF TypeOK,Inv84_4aa6_R7_1_I1,Inv5_c57a_R6_2_I1,Inv9_928b_R5_1_I2,Inv607_376d_R6_2_I1,Safety,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7767_5b71_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7767_5b71_R4_1_I2,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ HandleRequestVoteResponseAction => Inv7767_5b71_R4_1_I2' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7767_5b71_R4_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7767_5b71_R4_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv7767_5b71_R4_1_I2' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7767_5b71_R4_1_I2
  \* (Inv7767_5b71_R4_1_I2,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv7767_5b71_R4_1_I2 /\ HandleAppendEntriesResponseAction => Inv7767_5b71_R4_1_I2' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7767_5b71_R4_1_I2
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv84_4aa6_R7_1_I1
THEOREM L_38 == TypeOK /\ Inv15_1f30_R18_0_I1 /\ Inv84_4aa6_R7_1_I1 /\ Next => Inv84_4aa6_R7_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv84_4aa6_R7_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv15_1f30_R18_0_I1 /\ Inv84_4aa6_R7_1_I1 /\ RequestVoteAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,Inv15_1f30_R18_0_I1,RequestVoteAction,RequestVote,Inv84_4aa6_R7_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv84_4aa6_R7_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ UpdateTermAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv84_4aa6_R7_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv84_4aa6_R7_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ BecomeLeaderAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv84_4aa6_R7_1_I1
  \* (Inv84_4aa6_R7_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ ClientRequestAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv84_4aa6_R7_1_I1
  \* (Inv84_4aa6_R7_1_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ AppendEntriesAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv84_4aa6_R7_1_I1
  \* (Inv84_4aa6_R7_1_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ HandleRequestVoteRequestAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv84_4aa6_R7_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv84_4aa6_R7_1_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ HandleRequestVoteResponseAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv84_4aa6_R7_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv84_4aa6_R7_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv84_4aa6_R7_1_I1
  \* (Inv84_4aa6_R7_1_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv84_4aa6_R7_1_I1 /\ HandleAppendEntriesResponseAction => Inv84_4aa6_R7_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv84_4aa6_R7_1_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv15_1f30_R18_0_I1
THEOREM L_39 == TypeOK /\ Inv15_1f30_R18_0_I1 /\ Next => Inv15_1f30_R18_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv15_1f30_R18_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv15_1f30_R18_0_I1 /\ RequestVoteAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv15_1f30_R18_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_1f30_R18_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv15_1f30_R18_0_I1 /\ UpdateTermAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv15_1f30_R18_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv15_1f30_R18_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv15_1f30_R18_0_I1 /\ BecomeLeaderAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv15_1f30_R18_0_I1
  \* (Inv15_1f30_R18_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv15_1f30_R18_0_I1 /\ ClientRequestAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv15_1f30_R18_0_I1
  \* (Inv15_1f30_R18_0_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv15_1f30_R18_0_I1 /\ AppendEntriesAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv15_1f30_R18_0_I1
  \* (Inv15_1f30_R18_0_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv15_1f30_R18_0_I1 /\ HandleRequestVoteRequestAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv15_1f30_R18_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_1f30_R18_0_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv15_1f30_R18_0_I1 /\ HandleRequestVoteResponseAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv15_1f30_R18_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv15_1f30_R18_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv15_1f30_R18_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv15_1f30_R18_0_I1
  \* (Inv15_1f30_R18_0_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv15_1f30_R18_0_I1 /\ HandleAppendEntriesResponseAction => Inv15_1f30_R18_0_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv15_1f30_R18_0_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next


\*** Inv5_404d_R0_2_I1
THEOREM L_40 == TypeOK /\ Inv6746_404d_R2_1_I2 /\ Inv5_404d_R0_2_I1 /\ Next => Inv5_404d_R0_2_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5_404d_R0_2_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv5_404d_R0_2_I1 /\ RequestVoteAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5_404d_R0_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_404d_R0_2_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv5_404d_R0_2_I1 /\ UpdateTermAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5_404d_R0_2_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5_404d_R0_2_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6746_404d_R2_1_I2 /\ Inv5_404d_R0_2_I1 /\ BecomeLeaderAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,Inv6746_404d_R2_1_I2,BecomeLeaderAction,BecomeLeader,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv5_404d_R0_2_I1 /\ ClientRequestAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,AppendEntriesAction)
  <1>5. TypeOK /\ Inv5_404d_R0_2_I1 /\ AppendEntriesAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,HandleRequestVoteRequestAction)
  <1>6. TypeOK /\ Inv5_404d_R0_2_I1 /\ HandleRequestVoteRequestAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5_404d_R0_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_404d_R0_2_I1,HandleRequestVoteResponseAction)
  <1>7. TypeOK /\ Inv5_404d_R0_2_I1 /\ HandleRequestVoteResponseAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5_404d_R0_2_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5_404d_R0_2_I1,AcceptAppendEntriesRequestAppendAction)
  <1>8. TypeOK /\ Inv5_404d_R0_2_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5_404d_R0_2_I1
  \* (Inv5_404d_R0_2_I1,HandleAppendEntriesResponseAction)
  <1>9. TypeOK /\ Inv5_404d_R0_2_I1 /\ HandleAppendEntriesResponseAction => Inv5_404d_R0_2_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5_404d_R0_2_I1
<1>10. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_PrimaryHasEntriesItCreated
    <1>2. Init => Inv8509_2dd8_R0_0_I2 BY DEF Init, Inv8509_2dd8_R0_0_I2, IndGlobal
    <1>3. Init => Inv6390_7e0d_R1_1_I2 BY DEF Init, Inv6390_7e0d_R1_1_I2, IndGlobal
    <1>4. Init => Inv5215_bcfb_R0_1_I2 BY DEF Init, Inv5215_bcfb_R0_1_I2, IndGlobal
    <1>5. Init => Inv6746_404d_R2_1_I2 BY DEF Init, Inv6746_404d_R2_1_I2, IndGlobal
    <1>6. Init => Inv2_8e53_R5_0_I0 BY DEF Init, Inv2_8e53_R5_0_I0, IndGlobal
    <1>7. Init => Inv4_42ac_R5_1_I2 BY DEF Init, Inv4_42ac_R5_1_I2, IndGlobal
    <1>8. Init => Inv2_e30e_R12_0_I1 BY DEF Init, Inv2_e30e_R12_0_I1, IndGlobal
    <1>9. Init => Inv13_3715_R22_0_I0 BY DEF Init, Inv13_3715_R22_0_I0, IndGlobal
    <1>10. Init => Inv11_f533_R10_0_I0 BY DEF Init, Inv11_f533_R10_0_I0, IndGlobal
    <1>11. Init => Inv0_2c32_R8_1_I1 BY DEF Init, Inv0_2c32_R8_1_I1, IndGlobal
    <1>12. Init => Inv7_82b3_R12_1_I0 BY DEF Init, Inv7_82b3_R12_1_I0, IndGlobal
    <1>13. Init => Inv9_928b_R5_1_I2 BY DEF Init, Inv9_928b_R5_1_I2, IndGlobal
    <1>14. Init => Inv387_09bb_R9_0_I1 BY DEF Init, Inv387_09bb_R9_0_I1, IndGlobal
    <1>15. Init => Inv81_fe26_R20_0_I1 BY DEF Init, Inv81_fe26_R20_0_I1, IndGlobal
    <1>16. Init => Inv1630_58c9_R5_1_I2 BY DEF Init, Inv1630_58c9_R5_1_I2, IndGlobal
    <1>17. Init => Inv13_6261_R6_1_I1 BY DEF Init, Inv13_6261_R6_1_I1, IndGlobal
    <1>18. Init => Inv5771_fffd_R5_1_I2 BY DEF Init, Inv5771_fffd_R5_1_I2, IndGlobal
    <1>19. Init => Inv8096_c721_R2_2_I2 BY DEF Init, Inv8096_c721_R2_2_I2, IndGlobal
    <1>20. Init => Inv138_3acc_R6_1_I1 BY DEF Init, Inv138_3acc_R6_1_I1, IndGlobal
    <1>21. Init => Inv5_c57a_R6_2_I1 BY DEF Init, Inv5_c57a_R6_2_I1, IndGlobal, H_LogEntryInTermImpliesSafeAtTerm
    <1>22. Init => Inv7_2014_R15_0_I1 BY DEF Init, Inv7_2014_R15_0_I1, IndGlobal, H_LogEntryInTermImpliesSafeAtTermAppendEntries
    <1>23. Init => Inv12_0a54_R24_0_I1 BY DEF Init, Inv12_0a54_R24_0_I1, IndGlobal
    <1>24. Init => Inv379_f624_R24_0_I1 BY DEF Init, Inv379_f624_R24_0_I1, IndGlobal
    <1>25. Init => Inv31_73fd_R15_1_I1 BY DEF Init, Inv31_73fd_R15_1_I1, IndGlobal
    <1>26. Init => Inv10303_8d53_R26_3_I2 BY DEF Init, Inv10303_8d53_R26_3_I2, IndGlobal
    <1>27. Init => Inv17_e2fa_R26_0_I1 BY DEF Init, Inv17_e2fa_R26_0_I1, IndGlobal
    <1>28. Init => Inv11_dadc_R15_1_I1 BY DEF Init, Inv11_dadc_R15_1_I1, IndGlobal
    <1>29. Init => Inv21_3b9d_R26_2_I1 BY DEF Init, Inv21_3b9d_R26_2_I1, IndGlobal
    <1>30. Init => Inv18_bf9f_R24_0_I1 BY DEF Init, Inv18_bf9f_R24_0_I1, IndGlobal
    <1>31. Init => Inv6_9fea_R34_0_I1 BY DEF Init, Inv6_9fea_R34_0_I1, IndGlobal
    <1>32. Init => Inv107_791e_R15_2_I1 BY DEF Init, Inv107_791e_R15_2_I1, IndGlobal
    <1>33. Init => Inv3_9e78_R17_0_I0 BY DEF Init, Inv3_9e78_R17_0_I0, IndGlobal
    <1>34. Init => Inv0_5020_R27_1_I1 BY DEF Init, Inv0_5020_R27_1_I1, IndGlobal
    <1>35. Init => Inv607_376d_R6_2_I1 BY DEF Init, Inv607_376d_R6_2_I1, IndGlobal
    <1>36. Init => Inv7_1e2e_R6_3_I1 BY DEF Init, Inv7_1e2e_R6_3_I1, IndGlobal
    <1>37. Init => Inv7767_5b71_R4_1_I2 BY DEF Init, Inv7767_5b71_R4_1_I2, IndGlobal
    <1>38. Init => Inv84_4aa6_R7_1_I1 BY DEF Init, Inv84_4aa6_R7_1_I1, IndGlobal
    <1>39. Init => Inv15_1f30_R18_0_I1 BY DEF Init, Inv15_1f30_R18_0_I1, IndGlobal
    <1>40. Init => Inv5_404d_R0_2_I1 BY DEF Init, Inv5_404d_R0_2_I1, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12,<1>13,<1>14,<1>15,<1>16,<1>17,<1>18,<1>19,<1>20,<1>21,<1>22,<1>23,<1>24,<1>25,<1>26,<1>27,<1>28,<1>29,<1>30,<1>31,<1>32,<1>33,<1>34,<1>35,<1>36,<1>37,<1>38,<1>39,<1>40 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12,L_13,L_14,L_15,L_16,L_17,L_18,L_19,L_20,L_21,L_22,L_23,L_24,L_25,L_26,L_27,L_28,L_29,L_30,L_31,L_32,L_33,L_34,L_35,L_36,L_37,L_38,L_39,L_40 DEF Next, IndGlobal

================