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

\* If the intersection of two server sets is empty, then they can't both be quorums.
LEMMA EmptyIntersectionImpliesNotBothQuorums == 
    \A s1 \in SUBSET Server :
    \A s2 \in SUBSET Server :
        (s1 \cap s2 = {}) => ~(s1 \in Quorum /\ s2 \in Quorum)


LEMMA StaticQuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}

     
     

\* Proof Graph Stats
\* ==================
\* seed: 1
\* num proof graph nodes: 7
\* num proof obligations: 84

Safety == H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
Inv41_R0_0_I0 == (\A s,t \in Server : \A m \in requestVoteResponseMsgs :( /\ state[s] \in {Candidate,Leader} /\ t \in votesGranted[s]) => ~(/\ m.mterm = currentTerm[s] /\ m.msource = t /\ m.mdest # s /\ m.mvoteGranted))
Inv1566_R0_1_I1 == \A VARI \in Server : \A VARJ \in Server : ~((currentTerm[VARI] > currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv7_R1_0_I0 == (\A s \in Server : state[s] \in {Candidate,Leader} =>  (\A t \in votesGranted[s] :  /\ currentTerm[t] = currentTerm[s] => votedFor[t] = s ))
Inv0_R1_1_I0 == (\A mi,mj \in requestVoteResponseMsgs : (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted) => mi.mdest = mj.mdest)
Inv3_R1_2_I0 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv0_R3_0_I0 == (\A m \in requestVoteResponseMsgs : m.mtype = RequestVoteResponse =>  /\ (m.mvoteGranted /\ (currentTerm[m.msource] = m.mterm)) => votedFor[m.msource] = m.mdest)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  /\ H_LeaderHasVotesGrantedQuorum
  /\ Inv41_R0_0_I0
  /\ Inv7_R1_0_I0
  /\ Inv0_R3_0_I0
  /\ Inv3_R1_2_I0
  /\ Inv1566_R0_1_I1
  /\ Inv0_R1_1_I0


\* mean in-degree: 1.7142857142857142
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

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ RequestVoteAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF LastTerm,TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
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
      BY DEF Agree,TypeOK,Max,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
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
  <1>6. TypeOK /\ TypeOK /\ AppendEntriesAction => TypeOK' BY DEF TypeOK,AppendEntriesAction,AppendEntries,TypeOK
  \* (TypeOK,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction => TypeOK' 
    <2> SUFFICES ASSUME TypeOK /\ TypeOK /\ HandleRequestVoteRequestAction
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. (requestVoteRequestMsgs \in SUBSET RequestVoteRequestType)'
      BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. (requestVoteResponseMsgs \in SUBSET RequestVoteResponseType)'
      BY DEF TypeOK,LastTerm,HandleRequestVoteRequestAction,HandleRequestVoteRequest,TypeOK,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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


THEOREM L_A0 == TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ H_LeaderHasVotesGrantedQuorum /\ Inv41_R0_0_I0 /\ Safety /\ Next => Safety'
  <1> SUFFICES ASSUME TypeOK,
                      H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,
                      H_LeaderHasVotesGrantedQuorum,
                      Inv41_R0_0_I0,
                      Safety,
                      Next
               PROVE  Safety'
    OBVIOUS
   <1> USE A0,A1,A2,A3,A4,A5,A6,A7,StaticQuorumsOverlap, 
       FS_Singleton, FS_Difference, FS_Union, FS_Subset, AddingToQuorumRemainsQuorum
  <1> USE DEF H_CandidateWithVotesGrantedInTermImplyNoOtherLeader, H_LeaderHasVotesGrantedQuorum, Inv41_R0_0_I0
  <1>1. CASE RequestVoteAction
    <2> SUFFICES ASSUME NEW i \in Server,
                        RequestVote(i)
                 PROVE   (\A s,t \in Server :
        (/\ s # t
         /\ state[s] = Candidate
         /\ votesGranted[s] \in Quorum
         /\ currentTerm[s] = currentTerm[t]) =>
            state[t] # Leader)'
      BY <1>1 DEF RequestVoteAction, Safety, H_CandidateWithVotesGrantedInTermImplyNoOtherLeader 
         
    <2> QED
      <3> SUFFICES ASSUME NEW s \in Server', NEW t \in Server',
                          (/\ s # t
                           /\ state[s] = Candidate
                           /\ votesGranted[s] \in Quorum
                           /\ currentTerm[s] = currentTerm[t])'
                   PROVE  (state[t] # Leader)'
        OBVIOUS
      <3>1. CASE state[t] # Leader
         BY <3>1, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      <3>2. CASE state[t] = Leader /\ i # s
               BY <3>2, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      <3>3. CASE state[t] = Leader /\ i = s /\ state[i] = Leader
               BY <3>3, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      <3>4. CASE state[t] = Leader /\ i = s /\ state[i] \in {Follower,Candidate} /\ currentTerm[s] = currentTerm[t]
               BY <3>4, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      
      <3>5. CASE state[t] = Leader /\ i = s /\ state[i] \in {Follower,Candidate} /\ currentTerm[s] > currentTerm[t]
               BY <3>5, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      <3>6. CASE state[t] = Leader /\ i = s /\ state[i] \in {Follower,Candidate} /\ currentTerm[s] < currentTerm[t] - 1
               BY <3>6, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      <3>7. CASE state[t] = Leader /\ i = s /\ state[i] \in {Follower,Candidate} /\ currentTerm[s] = currentTerm[t] - 1
            <4>1. votesGranted'[s] = {s}
               BY <3>7, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
             <4>2. {s} \notin Quorum
                BY <3>7, <1>1 DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
             <4>3. votesGranted'[s] \notin Quorum
                    BY <4>1, <4>2
             <4>4. QED BY <4>1 , <4>3, <4>2                        
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7
        DEF LastTerm,TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Safety,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      
      
    
  <1>2. CASE UpdateTermAction
    BY <1>2 DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>3. CASE HandleRequestVoteRequestAction
    BY <1>3 DEF TypeOK,Inv1566_R0_1_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>4. CASE HandleRequestVoteResponseAction
    <2> SUFFICES ASSUME NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m)
                 PROVE  (\A s,t \in Server :
        (/\ s # t
         /\ state[s] = Candidate
         /\ votesGranted[s] \in Quorum
         /\ currentTerm[s] = currentTerm[t]) =>
            state[t] # Leader)'
      BY <1>4 DEF HandleRequestVoteResponseAction, Safety, H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
    <2> QED
      <3> SUFFICES ASSUME NEW s \in Server', NEW t \in Server',
                          (/\ s # t
                           /\ state[s] = Candidate
                           /\ votesGranted[s] \in Quorum
                           /\ currentTerm[s] = currentTerm[t])'
                   PROVE  (state[t] # Leader)'
        OBVIOUS     
      <3> QED
        BY <1>4 DEF H_VotesCantBeGrantedTwiceToCandidatesInSameTerm, H_LeaderHasVotesGrantedQuorum, Inv41_R0_0_I0,TypeOK,Inv1566_R0_1_I1,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,H_LeaderHasVotesGrantedQuorum,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
    
    
  <1>5. CASE BecomeLeaderAction
    <2> SUFFICES ASSUME NEW i \in Server,
                        BecomeLeader(i)
                 PROVE  Safety'
      BY <1>5 DEF BecomeLeaderAction
    <2> QED
      BY <1>5 DEF TypeOK,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,Inv1566_R0_1_I1,BecomeLeaderAction,BecomeLeader,H_CandidateWithVotesGrantedInTermImplyNoOtherLeader,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
    
  <1>6. CASE ClientRequestAction
    BY <1>6 DEF TypeOK,Inv1566_R0_1_I1,ClientRequestAction,ClientRequest,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>7. CASE AppendEntriesAction
    BY <1>7 DEF TypeOK,Inv1566_R0_1_I1,AppendEntriesAction,AppendEntries,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>8. CASE RejectAppendEntriesRequestAction
    BY <1>8 DEF TypeOK,Inv1566_R0_1_I1,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>9. CASE AcceptAppendEntriesRequestAppendAction
    BY <1>9 DEF TypeOK,Inv1566_R0_1_I1,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>10. CASE AcceptAppendEntriesRequestLearnCommitAction
    BY <1>10 DEF TypeOK,Inv1566_R0_1_I1,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>11. CASE HandleAppendEntriesResponseAction
    BY <1>11 DEF TypeOK,Inv1566_R0_1_I1,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>12. CASE AdvanceCommitIndexAction
    BY <1>12 DEF TypeOK,Inv1566_R0_1_I1,AdvanceCommitIndexAction,AdvanceCommitIndex,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>13. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Next
     

THEOREM L_A1 == TypeOK /\ H_LeaderHasVotesGrantedQuorum /\ Next => H_LeaderHasVotesGrantedQuorum'
  <1>. SUFFICES ASSUME TypeOK,
                      H_LeaderHasVotesGrantedQuorum,
                      Next
               PROVE  H_LeaderHasVotesGrantedQuorum'
    OBVIOUS
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7,
        StaticQuorumsOverlap, 
        FS_Singleton, FS_Union, FS_Subset, FS_Difference, AddingToQuorumRemainsQuorum
  <1>1. CASE RequestVoteAction
    BY <1>1 DEF TypeOK,Inv1566_R0_1_I1,Next,RequestVoteAction,RequestVote,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  <1>2. CASE UpdateTermAction
    <2> SUFFICES ASSUME NEW s \in Server',
                        (state[s] = Leader)'
                 PROVE  (votesGranted[s] \in Quorum)'
      BY DEF H_LeaderHasVotesGrantedQuorum
    <2> QED
      <3> SUFFICES ASSUME NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                          UpdateTerm(m.mterm, m.mdest)
                   PROVE  (votesGranted[s] \in Quorum)'
        BY <1>2 DEF UpdateTermAction
      <3> QED
        BY DEF TypeOK,Inv1566_R0_1_I1,UpdateTermAction,UpdateTerm,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
      
    
    
  <1>3. CASE HandleRequestVoteRequestAction
    BY <1>3 DEF TypeOK,Inv1566_R0_1_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>4. CASE HandleRequestVoteResponseAction
    <2> SUFFICES ASSUME NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW s \in Server',
                        (state[s] = Leader)'
                 PROVE  (votesGranted[s] \in Quorum)'
      BY <1>4 DEF H_LeaderHasVotesGrantedQuorum, HandleRequestVoteResponseAction
    <2>1. CASE state[s] # Leader
      BY <2>1, <1>4 DEF TypeOK,Inv1566_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
    <2>2. CASE state[s] = Leader /\ m.mdest = s
      BY <2>2, <1>4 DEF TypeOK,Inv1566_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
    <2>3. CASE state[s] = Leader /\ m.mdest # s
      BY <2>3, <1>4 DEF TypeOK,Inv1566_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
                
    <2> QED
      BY <2>1,<2>2,<2>3,<1>4 DEF TypeOK,Inv1566_R0_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
    
       
    
  <1>5. CASE BecomeLeaderAction
    BY <1>5 DEF TypeOK,Inv1566_R0_1_I1,BecomeLeaderAction,BecomeLeader,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>6. CASE ClientRequestAction
    BY <1>6 DEF TypeOK,Inv1566_R0_1_I1,ClientRequestAction,ClientRequest,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>7. CASE AppendEntriesAction
    BY <1>7 DEF TypeOK,Inv1566_R0_1_I1,AppendEntriesAction,AppendEntries,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>8. CASE RejectAppendEntriesRequestAction
    BY <1>8 DEF TypeOK,Inv1566_R0_1_I1,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>9. CASE AcceptAppendEntriesRequestAppendAction
    BY <1>9 DEF TypeOK,Inv1566_R0_1_I1,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>10. CASE AcceptAppendEntriesRequestLearnCommitAction
    BY <1>10 DEF TypeOK,Inv1566_R0_1_I1,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>11. CASE HandleAppendEntriesResponseAction
    BY <1>11 DEF TypeOK,Inv1566_R0_1_I1,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>12. CASE AdvanceCommitIndexAction
    BY <1>12 DEF TypeOK,Inv1566_R0_1_I1,AdvanceCommitIndexAction,AdvanceCommitIndex,H_LeaderHasVotesGrantedQuorum,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  <1>13. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Next
     


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Inv1566_R0_1_I1 /\ Inv41_R0_0_I0 /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ Next => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RequestVoteAction)
  <1>1. TypeOK /\ Inv1566_R0_1_I1 /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ RequestVoteAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,UpdateTermAction)
  <1>2. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ UpdateTermAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,UpdateTermAction,UpdateTerm,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,BecomeLeaderAction)
  <1>3. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ BecomeLeaderAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,ClientRequestAction)
  <1>4. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ ClientRequestAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,ClientRequestAction,ClientRequest,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AdvanceCommitIndexAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AppendEntriesAction)
  <1>6. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AppendEntriesAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AppendEntriesAction,AppendEntries,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ HandleRequestVoteRequestAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv41_R0_0_I0 /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ HandleRequestVoteResponseAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,Inv41_R0_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ RejectAppendEntriesRequestAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AcceptAppendEntriesRequestAppendAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ AcceptAppendEntriesRequestLearnCommitAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
  \* (H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ H_VotesCantBeGrantedTwiceToCandidatesInSameTerm /\ HandleAppendEntriesResponseAction => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm,H_OnePrimaryPerTerm
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv41_R0_0_I0
THEOREM L_2 == TypeOK /\ Inv3_R1_2_I0 /\ Inv7_R1_0_I0 /\ Inv0_R1_1_I0 /\ Inv41_R0_0_I0 /\ Next => Inv41_R0_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv41_R0_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_R1_2_I0 /\ Inv41_R0_0_I0 /\ RequestVoteAction => Inv41_R0_0_I0' BY DEF TypeOK,Inv3_R1_2_I0,RequestVoteAction,RequestVote,Inv41_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv41_R0_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv41_R0_0_I0 /\ UpdateTermAction => Inv41_R0_0_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv41_R0_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv41_R0_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv41_R0_0_I0 /\ BecomeLeaderAction => Inv41_R0_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv41_R0_0_I0 /\ ClientRequestAction => Inv41_R0_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv41_R0_0_I0 /\ AdvanceCommitIndexAction => Inv41_R0_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv41_R0_0_I0 /\ AppendEntriesAction => Inv41_R0_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv7_R1_0_I0 /\ Inv41_R0_0_I0 /\ HandleRequestVoteRequestAction => Inv41_R0_0_I0' BY DEF TypeOK,Inv7_R1_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv41_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv41_R0_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv0_R1_1_I0 /\ Inv41_R0_0_I0 /\ HandleRequestVoteResponseAction => Inv41_R0_0_I0' BY DEF TypeOK,Inv0_R1_1_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv41_R0_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv41_R0_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv41_R0_0_I0 /\ RejectAppendEntriesRequestAction => Inv41_R0_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv41_R0_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv41_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv41_R0_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv41_R0_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv41_R0_0_I0
  \* (Inv41_R0_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv41_R0_0_I0 /\ HandleAppendEntriesResponseAction => Inv41_R0_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv41_R0_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv7_R1_0_I0
THEOREM L_3 == TypeOK /\ Inv1566_R0_1_I1 /\ Inv1566_R0_1_I1 /\ Inv0_R3_0_I0 /\ Inv7_R1_0_I0 /\ Next => Inv7_R1_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv7_R1_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv1566_R0_1_I1 /\ Inv7_R1_0_I0 /\ RequestVoteAction => Inv7_R1_0_I0' BY DEF TypeOK,Inv1566_R0_1_I1,RequestVoteAction,RequestVote,Inv7_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_R1_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv1566_R0_1_I1 /\ Inv7_R1_0_I0 /\ UpdateTermAction => Inv7_R1_0_I0' BY DEF TypeOK,Inv1566_R0_1_I1,UpdateTermAction,UpdateTerm,Inv7_R1_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv7_R1_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv7_R1_0_I0 /\ BecomeLeaderAction => Inv7_R1_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv7_R1_0_I0 /\ ClientRequestAction => Inv7_R1_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv7_R1_0_I0 /\ AdvanceCommitIndexAction => Inv7_R1_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv7_R1_0_I0 /\ AppendEntriesAction => Inv7_R1_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv7_R1_0_I0 /\ HandleRequestVoteRequestAction => Inv7_R1_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv7_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv7_R1_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv0_R3_0_I0 /\ Inv7_R1_0_I0 /\ HandleRequestVoteResponseAction => Inv7_R1_0_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_R3_0_I0,
                        Inv7_R1_0_I0,
                        NEW m \in requestVoteResponseMsgs,
                        HandleRequestVoteResponse(m),
                        NEW s \in Server',
                        (state[s] \in {Candidate,Leader})',
                        NEW t \in (votesGranted[s])'
                 PROVE  (/\ currentTerm[t] = currentTerm[s] => votedFor[t] = s)'
      BY DEF HandleRequestVoteResponseAction, Inv7_R1_0_I0
    <2>1. (currentTerm[t] = currentTerm[s] => votedFor[t] = s)'
      <3> SUFFICES ASSUME (currentTerm[t] = currentTerm[s])'
                   PROVE  (votedFor[t] = s)'
        OBVIOUS
      <3>1. CASE m.mvoteGranted /\ m.mdest # s
              BY <3>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      <3>2. CASE m.mvoteGranted /\ m.mdest = s
        <4>1. votedFor[t] = m.mdest
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        <4>2. QED 
                BY <3>2,<4>1, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
        
      <3>3. CASE ~m.mvoteGranted
              BY <3>2, FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
      <3> QED
        BY <3>1,<3>2,<3>3,FS_Singleton, FS_Difference, FS_Subset, FS_Union, StaticQuorumsOverlap DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv7_R1_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
      
    <2>2. QED
      BY <2>1
  \* (Inv7_R1_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv7_R1_0_I0 /\ RejectAppendEntriesRequestAction => Inv7_R1_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv7_R1_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv7_R1_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv7_R1_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv7_R1_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv7_R1_0_I0
  \* (Inv7_R1_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv7_R1_0_I0 /\ HandleAppendEntriesResponseAction => Inv7_R1_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv7_R1_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv0_R3_0_I0
THEOREM L_4 == TypeOK /\ Inv3_R1_2_I0 /\ Inv3_R1_2_I0 /\ Inv0_R3_0_I0 /\ Next => Inv0_R3_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_R3_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_R1_2_I0 /\ Inv0_R3_0_I0 /\ RequestVoteAction => Inv0_R3_0_I0' BY DEF TypeOK,Inv3_R1_2_I0,RequestVoteAction,RequestVote,Inv0_R3_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R3_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_R1_2_I0 /\ Inv0_R3_0_I0 /\ UpdateTermAction => Inv0_R3_0_I0' BY DEF TypeOK,Inv3_R1_2_I0,UpdateTermAction,UpdateTerm,Inv0_R3_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R3_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_R3_0_I0 /\ BecomeLeaderAction => Inv0_R3_0_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_R3_0_I0 /\ ClientRequestAction => Inv0_R3_0_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv0_R3_0_I0 /\ AdvanceCommitIndexAction => Inv0_R3_0_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv0_R3_0_I0 /\ AppendEntriesAction => Inv0_R3_0_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv0_R3_0_I0 /\ HandleRequestVoteRequestAction => Inv0_R3_0_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R3_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R3_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv0_R3_0_I0 /\ HandleRequestVoteResponseAction => Inv0_R3_0_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_R3_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R3_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv0_R3_0_I0 /\ RejectAppendEntriesRequestAction => Inv0_R3_0_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv0_R3_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv0_R3_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv0_R3_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv0_R3_0_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv0_R3_0_I0
  \* (Inv0_R3_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv0_R3_0_I0 /\ HandleAppendEntriesResponseAction => Inv0_R3_0_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_R3_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv3_R1_2_I0
THEOREM L_5 == TypeOK /\ Inv3_R1_2_I0 /\ Next => Inv3_R1_2_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv3_R1_2_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv3_R1_2_I0 /\ RequestVoteAction => Inv3_R1_2_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv3_R1_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R1_2_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv3_R1_2_I0 /\ UpdateTermAction => Inv3_R1_2_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv3_R1_2_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv3_R1_2_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv3_R1_2_I0 /\ BecomeLeaderAction => Inv3_R1_2_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv3_R1_2_I0 /\ ClientRequestAction => Inv3_R1_2_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv3_R1_2_I0 /\ AdvanceCommitIndexAction => Inv3_R1_2_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv3_R1_2_I0 /\ AppendEntriesAction => Inv3_R1_2_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv3_R1_2_I0 /\ HandleRequestVoteRequestAction => Inv3_R1_2_I0' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv3_R1_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R1_2_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R1_2_I0 /\ HandleRequestVoteResponseAction => Inv3_R1_2_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv3_R1_2_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv3_R1_2_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv3_R1_2_I0 /\ RejectAppendEntriesRequestAction => Inv3_R1_2_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv3_R1_2_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv3_R1_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv3_R1_2_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv3_R1_2_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv3_R1_2_I0
  \* (Inv3_R1_2_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv3_R1_2_I0 /\ HandleAppendEntriesResponseAction => Inv3_R1_2_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv3_R1_2_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1566_R0_1_I1
THEOREM L_6 == TypeOK /\ Inv3_R1_2_I0 /\ Inv1566_R0_1_I1 /\ Next => Inv1566_R0_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1566_R0_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1566_R0_1_I1 /\ RequestVoteAction => Inv1566_R0_1_I1' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1566_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1566_R0_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1566_R0_1_I1 /\ UpdateTermAction => Inv1566_R0_1_I1' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1566_R0_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1566_R0_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1566_R0_1_I1 /\ BecomeLeaderAction => Inv1566_R0_1_I1' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1566_R0_1_I1 /\ ClientRequestAction => Inv1566_R0_1_I1' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1566_R0_1_I1 /\ AdvanceCommitIndexAction => Inv1566_R0_1_I1' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1566_R0_1_I1 /\ AppendEntriesAction => Inv1566_R0_1_I1' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1566_R0_1_I1 /\ HandleRequestVoteRequestAction => Inv1566_R0_1_I1' BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1566_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1566_R0_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv3_R1_2_I0 /\ Inv1566_R0_1_I1 /\ HandleRequestVoteResponseAction => Inv1566_R0_1_I1' BY DEF TypeOK,Inv3_R1_2_I0,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1566_R0_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1566_R0_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1566_R0_1_I1 /\ RejectAppendEntriesRequestAction => Inv1566_R0_1_I1' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1566_R0_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1566_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1566_R0_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1566_R0_1_I1' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1566_R0_1_I1
  \* (Inv1566_R0_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1566_R0_1_I1 /\ HandleAppendEntriesResponseAction => Inv1566_R0_1_I1' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1566_R0_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv0_R1_1_I0
THEOREM L_7 == TypeOK /\ Inv0_R3_0_I0 /\ Inv0_R1_1_I0 /\ Next => Inv0_R1_1_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_R1_1_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_R1_1_I0 /\ RequestVoteAction => Inv0_R1_1_I0' BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_R1_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R1_1_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_R1_1_I0 /\ UpdateTermAction => Inv0_R1_1_I0' BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_R1_1_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R1_1_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_R1_1_I0 /\ BecomeLeaderAction => Inv0_R1_1_I0' BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_R1_1_I0 /\ ClientRequestAction => Inv0_R1_1_I0' BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv0_R1_1_I0 /\ AdvanceCommitIndexAction => Inv0_R1_1_I0' BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv0_R1_1_I0 /\ AppendEntriesAction => Inv0_R1_1_I0' BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv0_R3_0_I0 /\ Inv0_R1_1_I0 /\ HandleRequestVoteRequestAction => Inv0_R1_1_I0' 
    <2> SUFFICES ASSUME TypeOK,
                        Inv0_R3_0_I0,
                        Inv0_R1_1_I0,
                        NEW m \in requestVoteRequestMsgs,
                        HandleRequestVoteRequest(m),
                        NEW mi \in requestVoteResponseMsgs', NEW mj \in requestVoteResponseMsgs',
                        (/\ mi.mterm = mj.mterm /\ mi.msource = mj.msource /\ mi.mvoteGranted /\ mj.mvoteGranted)'
                 PROVE  (mi.mdest = mj.mdest)'
      BY DEF HandleRequestVoteRequestAction, Inv0_R1_1_I0
    <2>1. CASE m.mterm # currentTerm[m.mdest]
        BY <2>1 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>2. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \notin {Nil, m.msource}
            BY <2>2 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
    <2>3. CASE m.mterm = currentTerm[m.mdest] /\ votedFor[m.mdest] \in {Nil, m.msource}
        <3>1. CASE m.mdest # mi.msource
            BY <2>3,<3>1 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         \* m is the vote request message so its dest is the one receivign the vote request.         
         <3>2. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] # mi.mterm
                BY <2>3,<3>2 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>3. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest # mi.msource
                BY <2>3,<3>3 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>4. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \in requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>4 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>2. votedFor[mi.msource] = mi.mdest
                BY <4>1, <2>3,<3>4 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED 
                BY <4>1, <4>2,<3>4,<2>3 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>5. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \notin requestVoteResponseMsgs
            <4>1. currentTerm[mi.msource] = mi.mterm /\ mi.mvoteGranted
                BY <2>3,<3>5 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            <4>3. QED BY <4>1, <2>3,<3>5 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
         <3>6. CASE m.mdest = mi.msource /\ currentTerm[m.mdest] = mi.mterm /\ m.mdest = mi.msource /\ mi \notin requestVoteResponseMsgs /\ mj \in requestVoteResponseMsgs
            <4>3. QED BY <3>6 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
            
         <3>. QED BY <3>1, <3>2, <3>3,<3>4,<3>5,<3>6
    <2> QED
      BY <2>1, <2>2, <2>3 DEF TypeOK,Inv0_R3_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R1_1_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv0_R1_1_I0 /\ HandleRequestVoteResponseAction => Inv0_R1_1_I0' BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_R1_1_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R1_1_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv0_R1_1_I0 /\ RejectAppendEntriesRequestAction => Inv0_R1_1_I0' BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv0_R1_1_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv0_R1_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv0_R1_1_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv0_R1_1_I0' BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv0_R1_1_I0
  \* (Inv0_R1_1_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv0_R1_1_I0 /\ HandleAppendEntriesResponseAction => Inv0_R1_1_I0' BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_R1_1_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1> Init => Safety BY DEF Init, Safety, TypeOK, IndGlobal, H_CandidateWithVotesGrantedInTermImplyNoOtherLeader
    <1> Init => H_LeaderHasVotesGrantedQuorum BY DEF Init, H_LeaderHasVotesGrantedQuorum, TypeOK, IndGlobal
    <1>1. Init => H_VotesCantBeGrantedTwiceToCandidatesInSameTerm BY DEF Init, Safety, IndGlobal,H_VotesCantBeGrantedTwiceToCandidatesInSameTerm
    <1>2. Init => Inv41_R0_0_I0 BY DEF Init, Inv41_R0_0_I0, IndGlobal
    <1>3. Init => Inv7_R1_0_I0 BY DEF Init, Inv7_R1_0_I0, IndGlobal
    <1>4. Init => Inv0_R3_0_I0 BY DEF Init, Inv0_R3_0_I0, IndGlobal
    <1>5. Init => Inv3_R1_2_I0 BY DEF Init, Inv3_R1_2_I0, IndGlobal
    <1>6. Init => Inv1566_R0_1_I1 BY DEF Init, Inv1566_R0_1_I1, IndGlobal
    <1>7. Init => Inv0_R1_1_I0 BY DEF Init, Inv0_R1_1_I0, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_A0,L_A1 DEF Next, IndGlobal



====