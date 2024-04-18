--------------------------------- MODULE AsyncRaft_IndProofs ---------------------------------
EXTENDS AsyncRaft,TLAPS

\* Proof Graph Stats
\* ==================
\* seed: 6
\* num proof graph nodes: 12
\* num proof obligations: 144
Safety == H_OnePrimaryPerTerm
Inv8728_R0_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])))
Inv5810_R1_0_I2 == \A VARI \in Server : \A VARJ \in Server : (votesGranted[VARI] \cap votesGranted[VARJ] = {}) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Candidate))))
Inv1900_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~((state[VARI] = Leader)) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv10_R2_0_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv5485_R3_0_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~((state[VARI] = Candidate)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv6_R3_1_I2 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv1230_R3_1_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted) \/ (~(votedFor[VARJ] = VARI))
Inv5459_R3_1_I2 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : (votedFor[VARI] = VARI) \/ (~(currentTerm[VARREQVM.msource] = VARREQVM.mterm)) \/ (~(VARREQVM.msource = VARI))
Inv645_R5_0_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : ~(VARREQVM.mlastLogTerm >= currentTerm[VARI]) \/ (~(VARREQVM.msource = VARI))
Inv1_R7_0_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~(votedFor[VARI] = VARJ))
Inv1_R8_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv8728_R0_0_I2
  /\ Inv5810_R1_0_I2
  /\ Inv10_R2_0_I1
  /\ Inv1900_R1_1_I1
  /\ Inv5485_R3_0_I2
  /\ Inv645_R5_0_I1
  /\ Inv6_R3_1_I2
  /\ Inv1230_R3_1_I2
  /\ Inv1_R7_0_I1
  /\ Inv1_R8_0_I0
  /\ Inv5459_R3_1_I2


\* mean in-degree: 1.25
\* median in-degree: 1
\* max in-degree: 4
\* min in-degree: 0
\* mean variable slice size: 0

ASSUME A0 == IsFiniteSet(Server)
ASSUME A1 == Nil \notin Server
ASSUME A2 == (Leader # Follower) /\ (Leader # Candidate)
ASSUME A3 == (Follower # Candidate)
ASSUME A4 == Server = Server
ASSUME A5 == Quorum \subseteq Server
ASSUME A6 == MaxLogLen \in Nat
ASSUME A7 == MaxTerm \in Nat

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (TypeOK,RequestVoteAction)
  <1>1. TypeOK /\ TypeOK /\ RequestVoteAction => TypeOK'
       BY DEF TypeOK,RequestVoteAction,RequestVote,TypeOK,RequestVoteResponseType, Terms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,UpdateTermAction)
  <1>2. TypeOK /\ TypeOK /\ UpdateTermAction => TypeOK'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,TypeOK,RequestVoteResponseType, Terms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (TypeOK,BecomeLeaderAction)
  <1>3. TypeOK /\ TypeOK /\ BecomeLeaderAction => TypeOK'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,TypeOK
  \* (TypeOK,ClientRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ClientRequestAction => TypeOK'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,TypeOK
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
      BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,TypeOK
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
THEOREM L_1 == TypeOK /\ Inv8728_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7 DEF H_OnePrimaryPerTerm
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Safety
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8728_R0_0_I2 /\ Safety /\ BecomeLeaderAction => Safety'
       BY DEF TypeOK,Inv8728_R0_0_I2,BecomeLeaderAction,BecomeLeader,Safety
  \* (Safety,ClientRequestAction)
  <1>4. TypeOK /\ Safety /\ ClientRequestAction => Safety'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Safety
  \* (Safety,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Safety /\ AdvanceCommitIndexAction => Safety'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Safety
  \* (Safety,AppendEntriesAction)
  <1>6. TypeOK /\ Safety /\ AppendEntriesAction => Safety'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Safety
  \* (Safety,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Safety /\ HandleRequestVoteRequestAction => Safety'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Safety,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Safety /\ HandleRequestVoteResponseAction => Safety'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Safety,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Safety,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Safety /\ RejectAppendEntriesRequestAction => Safety'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Safety
  \* (Safety,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Safety /\ AcceptAppendEntriesRequestAppendAction => Safety'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Safety
  \* (Safety,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Safety /\ AcceptAppendEntriesRequestLearnCommitAction => Safety'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Safety
  \* (Safety,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Safety /\ HandleAppendEntriesResponseAction => Safety'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Safety
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv8728_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv5810_R1_0_I2 /\ Inv1900_R1_1_I1 /\ Inv8728_R0_0_I2 /\ Next => Inv8728_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8728_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv8728_R0_0_I2 /\ RequestVoteAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv8728_R0_0_I2 /\ UpdateTermAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5810_R1_0_I2 /\ Inv8728_R0_0_I2 /\ BecomeLeaderAction => Inv8728_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv5810_R1_0_I2,
                        Inv8728_R0_0_I2,
                        TRUE,
                        NEW i \in Server,
                        BecomeLeader(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF BecomeLeaderAction, Inv8728_R0_0_I2
    <2> QED
      BY DEF TypeOK,Inv5810_R1_0_I2,BecomeLeaderAction,BecomeLeader,Inv8728_R0_0_I2,RequestVoteResponseType, Terms,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
       
  \* (Inv8728_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv8728_R0_0_I2 /\ ClientRequestAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv8728_R0_0_I2 /\ AdvanceCommitIndexAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv8728_R0_0_I2 /\ AppendEntriesAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv8728_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8728_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8728_R0_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1900_R1_1_I1 /\ Inv8728_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,Inv1900_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8728_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8728_R0_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv8728_R0_0_I2 /\ RejectAppendEntriesRequestAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv8728_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv8728_R0_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv8728_R0_0_I2
  \* (Inv8728_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv8728_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv8728_R0_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8728_R0_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5810_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv10_R2_0_I1 /\ Inv5810_R1_0_I2 /\ Next => Inv5810_R1_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5810_R1_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_0_I1 /\ Inv5810_R1_0_I2 /\ RequestVoteAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,Inv10_R2_0_I1,RequestVoteAction,RequestVote,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv5810_R1_0_I2 /\ UpdateTermAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5810_R1_0_I2 /\ BecomeLeaderAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv5810_R1_0_I2 /\ ClientRequestAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv5810_R1_0_I2 /\ AdvanceCommitIndexAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv5810_R1_0_I2 /\ AppendEntriesAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv5810_R1_0_I2 /\ HandleRequestVoteRequestAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5810_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5810_R1_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv5810_R1_0_I2 /\ HandleRequestVoteResponseAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5810_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5810_R1_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv5810_R1_0_I2 /\ RejectAppendEntriesRequestAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv5810_R1_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv5810_R1_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv5810_R1_0_I2
  \* (Inv5810_R1_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv5810_R1_0_I2 /\ HandleAppendEntriesResponseAction => Inv5810_R1_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5810_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv10_R2_0_I1 /\ Next => Inv10_R2_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R2_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_0_I1 /\ RequestVoteAction => Inv10_R2_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R2_0_I1 /\ UpdateTermAction => Inv10_R2_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv10_R2_0_I1 /\ BecomeLeaderAction => Inv10_R2_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv10_R2_0_I1 /\ ClientRequestAction => Inv10_R2_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv10_R2_0_I1 /\ AdvanceCommitIndexAction => Inv10_R2_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv10_R2_0_I1 /\ AppendEntriesAction => Inv10_R2_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv10_R2_0_I1 /\ HandleRequestVoteRequestAction => Inv10_R2_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv10_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R2_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv10_R2_0_I1 /\ HandleRequestVoteResponseAction => Inv10_R2_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv10_R2_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv10_R2_0_I1 /\ RejectAppendEntriesRequestAction => Inv10_R2_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv10_R2_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv10_R2_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv10_R2_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv10_R2_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv10_R2_0_I1
  \* (Inv10_R2_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv10_R2_0_I1 /\ HandleAppendEntriesResponseAction => Inv10_R2_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv10_R2_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1900_R1_1_I1
THEOREM L_5 == TypeOK /\ Inv5485_R3_0_I2 /\ Inv6_R3_1_I2 /\ Inv1230_R3_1_I2 /\ Inv5459_R3_1_I2 /\ Inv1900_R1_1_I1 /\ Next => Inv1900_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1900_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1900_R1_1_I1 /\ RequestVoteAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1900_R1_1_I1 /\ UpdateTermAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5485_R3_0_I2 /\ Inv1900_R1_1_I1 /\ BecomeLeaderAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,Inv5485_R3_0_I2,BecomeLeaderAction,BecomeLeader,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1900_R1_1_I1 /\ ClientRequestAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1900_R1_1_I1 /\ AdvanceCommitIndexAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1900_R1_1_I1 /\ AppendEntriesAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R3_1_I2 /\ Inv1230_R3_1_I2 /\ Inv5459_R3_1_I2 /\ Inv1900_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,Inv6_R3_1_I2,Inv1230_R3_1_I2,Inv5459_R3_1_I2,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1900_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1900_R1_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1900_R1_1_I1 /\ HandleRequestVoteResponseAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1900_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1900_R1_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1900_R1_1_I1 /\ RejectAppendEntriesRequestAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1900_R1_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1900_R1_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1900_R1_1_I1
  \* (Inv1900_R1_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1900_R1_1_I1 /\ HandleAppendEntriesResponseAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1900_R1_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5485_R3_0_I2
THEOREM L_6 == TypeOK /\ Inv645_R5_0_I1 /\ Inv5485_R3_0_I2 /\ Next => Inv5485_R3_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5485_R3_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5485_R3_0_I2 /\ RequestVoteAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5485_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv5485_R3_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv5485_R3_0_I2 /\ UpdateTermAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5485_R3_0_I2 /\ BecomeLeaderAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv5485_R3_0_I2 /\ ClientRequestAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv5485_R3_0_I2 /\ AdvanceCommitIndexAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv5485_R3_0_I2 /\ AppendEntriesAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv645_R5_0_I1 /\ Inv5485_R3_0_I2 /\ HandleRequestVoteRequestAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,Inv645_R5_0_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5485_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5485_R3_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv5485_R3_0_I2 /\ HandleRequestVoteResponseAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5485_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5485_R3_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv5485_R3_0_I2 /\ RejectAppendEntriesRequestAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv5485_R3_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv5485_R3_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv5485_R3_0_I2
  \* (Inv5485_R3_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv5485_R3_0_I2 /\ HandleAppendEntriesResponseAction => Inv5485_R3_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5485_R3_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv645_R5_0_I1
THEOREM L_7 == TypeOK /\ Inv645_R5_0_I1 /\ Next => Inv645_R5_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv645_R5_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv645_R5_0_I1 /\ RequestVoteAction => Inv645_R5_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv645_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv645_R5_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv645_R5_0_I1 /\ UpdateTermAction => Inv645_R5_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv645_R5_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv645_R5_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv645_R5_0_I1 /\ BecomeLeaderAction => Inv645_R5_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv645_R5_0_I1 /\ ClientRequestAction => Inv645_R5_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv645_R5_0_I1 /\ AdvanceCommitIndexAction => Inv645_R5_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv645_R5_0_I1 /\ AppendEntriesAction => Inv645_R5_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv645_R5_0_I1 /\ HandleRequestVoteRequestAction => Inv645_R5_0_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv645_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv645_R5_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv645_R5_0_I1 /\ HandleRequestVoteResponseAction => Inv645_R5_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv645_R5_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv645_R5_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv645_R5_0_I1 /\ RejectAppendEntriesRequestAction => Inv645_R5_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv645_R5_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv645_R5_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv645_R5_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv645_R5_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv645_R5_0_I1
  \* (Inv645_R5_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv645_R5_0_I1 /\ HandleAppendEntriesResponseAction => Inv645_R5_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv645_R5_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6_R3_1_I2
THEOREM L_8 == TypeOK /\ Inv6_R3_1_I2 /\ Next => Inv6_R3_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_R3_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R3_1_I2 /\ RequestVoteAction => Inv6_R3_1_I2'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_R3_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R3_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R3_1_I2 /\ UpdateTermAction => Inv6_R3_1_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_R3_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R3_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_R3_1_I2 /\ BecomeLeaderAction => Inv6_R3_1_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_R3_1_I2 /\ ClientRequestAction => Inv6_R3_1_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6_R3_1_I2 /\ AdvanceCommitIndexAction => Inv6_R3_1_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6_R3_1_I2 /\ AppendEntriesAction => Inv6_R3_1_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R3_1_I2 /\ HandleRequestVoteRequestAction => Inv6_R3_1_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_R3_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R3_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R3_1_I2 /\ HandleRequestVoteResponseAction => Inv6_R3_1_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_R3_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R3_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6_R3_1_I2 /\ RejectAppendEntriesRequestAction => Inv6_R3_1_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6_R3_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6_R3_1_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6_R3_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6_R3_1_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6_R3_1_I2
  \* (Inv6_R3_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6_R3_1_I2 /\ HandleAppendEntriesResponseAction => Inv6_R3_1_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_R3_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1230_R3_1_I2
THEOREM L_9 == TypeOK /\ Inv6_R3_1_I2 /\ Inv1_R7_0_I1 /\ Inv1_R7_0_I1 /\ Inv6_R3_1_I2 /\ Inv1230_R3_1_I2 /\ Next => Inv1230_R3_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1230_R3_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R3_1_I2 /\ Inv1_R7_0_I1 /\ Inv1230_R3_1_I2 /\ RequestVoteAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,Inv6_R3_1_I2,Inv1_R7_0_I1,RequestVoteAction,RequestVote,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R7_0_I1 /\ Inv6_R3_1_I2 /\ Inv1230_R3_1_I2 /\ UpdateTermAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,Inv1_R7_0_I1,Inv6_R3_1_I2,UpdateTermAction,UpdateTerm,Inv1230_R3_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1230_R3_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1230_R3_1_I2 /\ BecomeLeaderAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv1230_R3_1_I2 /\ ClientRequestAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1230_R3_1_I2 /\ AdvanceCommitIndexAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1230_R3_1_I2 /\ AppendEntriesAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1230_R3_1_I2 /\ HandleRequestVoteRequestAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1230_R3_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1230_R3_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1230_R3_1_I2 /\ HandleRequestVoteResponseAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1230_R3_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1230_R3_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1230_R3_1_I2 /\ RejectAppendEntriesRequestAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1230_R3_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1230_R3_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1230_R3_1_I2
  \* (Inv1230_R3_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1230_R3_1_I2 /\ HandleAppendEntriesResponseAction => Inv1230_R3_1_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1230_R3_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_R7_0_I1
THEOREM L_10 == TypeOK /\ Inv1_R8_0_I0 /\ Inv1_R7_0_I1 /\ Next => Inv1_R7_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1_R7_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1_R7_0_I1 /\ RequestVoteAction => Inv1_R7_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R7_0_I1 /\ UpdateTermAction => Inv1_R7_0_I1'
    <2> SUFFICES ASSUME TypeOK,
                        Inv1_R7_0_I1,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m.mterm, m.mdest),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~(votedFor[VARI] = VARJ)))'
      BY DEF Inv1_R7_0_I1, UpdateTermAction
    <2> QED
      BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1_R7_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
       
  \* (Inv1_R7_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1_R7_0_I1 /\ BecomeLeaderAction => Inv1_R7_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1_R7_0_I1 /\ ClientRequestAction => Inv1_R7_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1_R7_0_I1 /\ AdvanceCommitIndexAction => Inv1_R7_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1_R7_0_I1 /\ AppendEntriesAction => Inv1_R7_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1_R8_0_I0 /\ Inv1_R7_0_I1 /\ HandleRequestVoteRequestAction => Inv1_R7_0_I1'
       BY DEF TypeOK,Inv1_R8_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1_R7_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R7_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R7_0_I1 /\ HandleRequestVoteResponseAction => Inv1_R7_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1_R7_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R7_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1_R7_0_I1 /\ RejectAppendEntriesRequestAction => Inv1_R7_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1_R7_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1_R7_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1_R7_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1_R7_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1_R7_0_I1
  \* (Inv1_R7_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1_R7_0_I1 /\ HandleAppendEntriesResponseAction => Inv1_R7_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1_R7_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_R8_0_I0
THEOREM L_11 == TypeOK /\ Inv1_R8_0_I0 /\ Next => Inv1_R8_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1_R8_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv1_R8_0_I0 /\ RequestVoteAction => Inv1_R8_0_I0'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1_R8_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R8_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R8_0_I0 /\ UpdateTermAction => Inv1_R8_0_I0'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1_R8_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R8_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1_R8_0_I0 /\ BecomeLeaderAction => Inv1_R8_0_I0'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv1_R8_0_I0 /\ ClientRequestAction => Inv1_R8_0_I0'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1_R8_0_I0 /\ AdvanceCommitIndexAction => Inv1_R8_0_I0'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1_R8_0_I0 /\ AppendEntriesAction => Inv1_R8_0_I0'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1_R8_0_I0 /\ HandleRequestVoteRequestAction => Inv1_R8_0_I0'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R8_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R8_0_I0 /\ HandleRequestVoteResponseAction => Inv1_R8_0_I0'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1_R8_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R8_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1_R8_0_I0 /\ RejectAppendEntriesRequestAction => Inv1_R8_0_I0'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1_R8_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv1_R8_0_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1_R8_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1_R8_0_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1_R8_0_I0
  \* (Inv1_R8_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1_R8_0_I0 /\ HandleAppendEntriesResponseAction => Inv1_R8_0_I0'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1_R8_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv5459_R3_1_I2
THEOREM L_12 == TypeOK /\ Inv1_R8_0_I0 /\ Inv5459_R3_1_I2 /\ Next => Inv5459_R3_1_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv5459_R3_1_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv5459_R3_1_I2 /\ RequestVoteAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R8_0_I0 /\ Inv5459_R3_1_I2 /\ UpdateTermAction => Inv5459_R3_1_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv1_R8_0_I0,
                        Inv5459_R3_1_I2,
                        TRUE,
                        NEW m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs,
                        UpdateTerm(m.mterm, m.mdest),
                        NEW VARI \in Server',
                        NEW VARREQVM \in requestVoteRequestMsgs'
                 PROVE  ((votedFor[VARI] = VARI) \/ (~(currentTerm[VARREQVM.msource] = VARREQVM.mterm)) \/ (~(VARREQVM.msource = VARI)))'
      BY DEF Inv5459_R3_1_I2, UpdateTermAction
    <2> QED
      BY DEF TypeOK,Inv1_R8_0_I0,UpdateTermAction,UpdateTerm,Inv5459_R3_1_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
       
  \* (Inv5459_R3_1_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv5459_R3_1_I2 /\ BecomeLeaderAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv5459_R3_1_I2 /\ ClientRequestAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv5459_R3_1_I2 /\ AdvanceCommitIndexAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv5459_R3_1_I2 /\ AppendEntriesAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv5459_R3_1_I2 /\ HandleRequestVoteRequestAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv5459_R3_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5459_R3_1_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv5459_R3_1_I2 /\ HandleRequestVoteResponseAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv5459_R3_1_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv5459_R3_1_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv5459_R3_1_I2 /\ RejectAppendEntriesRequestAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv5459_R3_1_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv5459_R3_1_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv5459_R3_1_I2
  \* (Inv5459_R3_1_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv5459_R3_1_I2 /\ HandleAppendEntriesResponseAction => Inv5459_R3_1_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv5459_R3_1_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7 
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal,H_OnePrimaryPerTerm
    <1>2. Init => Inv8728_R0_0_I2 BY DEF Init, Inv8728_R0_0_I2, IndGlobal
    <1>3. Init => Inv5810_R1_0_I2 BY DEF Init, Inv5810_R1_0_I2, IndGlobal
    <1>4. Init => Inv10_R2_0_I1 BY DEF Init, Inv10_R2_0_I1, IndGlobal
    <1>5. Init => Inv1900_R1_1_I1 BY DEF Init, Inv1900_R1_1_I1, IndGlobal
    <1>6. Init => Inv5485_R3_0_I2 BY DEF Init, Inv5485_R3_0_I2, IndGlobal
    <1>7. Init => Inv645_R5_0_I1 BY DEF Init, Inv645_R5_0_I1, IndGlobal
    <1>8. Init => Inv6_R3_1_I2 BY DEF Init, Inv6_R3_1_I2, IndGlobal
    <1>9. Init => Inv1230_R3_1_I2 BY DEF Init, Inv1230_R3_1_I2, IndGlobal
    <1>10. Init => Inv1_R7_0_I1 BY DEF Init, Inv1_R7_0_I1, IndGlobal
    <1>11. Init => Inv1_R8_0_I0 BY DEF Init, Inv1_R8_0_I0, IndGlobal
    <1>12. Init => Inv5459_R3_1_I2 BY DEF Init, Inv5459_R3_1_I2, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11,L_12 DEF Next, IndGlobal


===============================================================================