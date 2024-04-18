--------------------------------- MODULE AsyncRaft_IndProofs ---------------------------------
EXTENDS AsyncRaft,TLAPS

\* Proof Graph Stats
\* ==================
\* seed: 6
\* num proof graph nodes: 11
\* num proof obligations: 132
Safety == H_OnePrimaryPerTerm
Inv8807_R0_0_I2 == \A VARI \in Server : \A VARJ \in Server : ((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])))
Inv6321_R1_0_I2 == \A VARI \in Server : \A VARJ \in Server : (votesGranted[VARI] \cap votesGranted[VARJ] = {}) \/ (~((state[VARI] = Candidate /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ])) \/ (~((state[VARJ] = Candidate))))
Inv1900_R1_1_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~((state[VARI] = Leader)) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv10_R2_0_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~((state[VARI] \in {Leader,Candidate} /\ VARJ \in votesGranted[VARI])))
Inv6184_R3_0_I2 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~((state[VARI] = Candidate)) \/ (~(votesGranted[VARI] \in Quorum)) \/ (~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted))
Inv984_R3_1_I1 == \A VARI \in Server : \A VARREQVM \in requestVoteRequestMsgs : ~(VARREQVM.mlastLogTerm >= currentTerm[VARI]) \/ (~(VARREQVM.mterm = currentTerm[VARI]))
Inv6_R3_1_I1 == \A VARREQVRES \in requestVoteResponseMsgs : (currentTerm[VARREQVRES.msource] >= VARREQVRES.mterm)
Inv1209_R3_1_I1 == \A VARI \in Server : \A VARJ \in Server : \A VARREQVRES \in requestVoteResponseMsgs : ~(VARREQVRES.mterm = currentTerm[VARI] /\ VARREQVRES.msource = VARJ /\ VARREQVRES.mdest # VARI /\ VARREQVRES.mvoteGranted) \/ (~(votedFor[VARJ] = VARI))
Inv0_R8_0_I1 == \A VARI \in Server : \A VARJ \in Server : ((currentTerm[VARI] <= currentTerm[VARJ])) \/ (~(votedFor[VARI] = VARJ))
Inv1_R9_0_I0 == \A VARREQVM \in requestVoteRequestMsgs : (currentTerm[VARREQVM.msource] >= VARREQVM.mterm)

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv8807_R0_0_I2
  /\ Inv6321_R1_0_I2
  /\ Inv10_R2_0_I1
  /\ Inv6_R3_1_I1
  /\ Inv1900_R1_1_I1
  /\ Inv6184_R3_0_I2
  /\ Inv984_R3_1_I1
  /\ Inv1209_R3_1_I1
  /\ Inv0_R8_0_I1
  /\ Inv1_R9_0_I0


\* mean in-degree: 1.0909090909090908
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
THEOREM L_1 == TypeOK /\ Inv8807_R0_0_I2 /\ Safety /\ Next => Safety'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Safety,RequestVoteAction)
  <1>1. TypeOK /\ Safety /\ RequestVoteAction => Safety'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,UpdateTermAction)
  <1>2. TypeOK /\ Safety /\ UpdateTermAction => Safety'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Safety,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType,H_OnePrimaryPerTerm
  \* (Safety,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv8807_R0_0_I2 /\ Safety /\ BecomeLeaderAction => Safety'
       BY DEF TypeOK,Inv8807_R0_0_I2,BecomeLeaderAction,BecomeLeader,Safety,H_OnePrimaryPerTerm
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


\*** Inv8807_R0_0_I2
THEOREM L_2 == TypeOK /\ Inv6321_R1_0_I2 /\ Inv1900_R1_1_I1 /\ Inv8807_R0_0_I2 /\ Next => Inv8807_R0_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv8807_R0_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv8807_R0_0_I2 /\ RequestVoteAction => Inv8807_R0_0_I2'
    <2> SUFFICES ASSUME TypeOK,
                        Inv8807_R0_0_I2,
                        TRUE,
                        NEW i \in Server,
                        RequestVote(i),
                        NEW VARI \in Server',
                        NEW VARJ \in Server'
                 PROVE  (((state[VARJ] = Follower)) \/ (~(votesGranted[VARJ] \in Quorum)) \/ (~((state[VARI] = Leader /\ VARI # VARJ /\ currentTerm[VARI] = currentTerm[VARJ]))))'
      BY DEF Inv8807_R0_0_I2, RequestVoteAction
    <2> QED
      BY DEF TypeOK,RequestVoteAction,RequestVote,Inv8807_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
       
  \* (Inv8807_R0_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv8807_R0_0_I2 /\ UpdateTermAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv8807_R0_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv8807_R0_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6321_R1_0_I2 /\ Inv8807_R0_0_I2 /\ BecomeLeaderAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,Inv6321_R1_0_I2,BecomeLeaderAction,BecomeLeader,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv8807_R0_0_I2 /\ ClientRequestAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv8807_R0_0_I2 /\ AdvanceCommitIndexAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv8807_R0_0_I2 /\ AppendEntriesAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv8807_R0_0_I2 /\ HandleRequestVoteRequestAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv8807_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8807_R0_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1900_R1_1_I1 /\ Inv8807_R0_0_I2 /\ HandleRequestVoteResponseAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,Inv1900_R1_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv8807_R0_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv8807_R0_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv8807_R0_0_I2 /\ RejectAppendEntriesRequestAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv8807_R0_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv8807_R0_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv8807_R0_0_I2
  \* (Inv8807_R0_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv8807_R0_0_I2 /\ HandleAppendEntriesResponseAction => Inv8807_R0_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv8807_R0_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv6321_R1_0_I2
THEOREM L_3 == TypeOK /\ Inv10_R2_0_I1 /\ Inv6321_R1_0_I2 /\ Next => Inv6321_R1_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6321_R1_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_0_I1 /\ Inv6321_R1_0_I2 /\ RequestVoteAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,Inv10_R2_0_I1,RequestVoteAction,RequestVote,Inv6321_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6321_R1_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6321_R1_0_I2 /\ UpdateTermAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6321_R1_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6321_R1_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6321_R1_0_I2 /\ BecomeLeaderAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6321_R1_0_I2 /\ ClientRequestAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6321_R1_0_I2 /\ AdvanceCommitIndexAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6321_R1_0_I2 /\ AppendEntriesAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6321_R1_0_I2 /\ HandleRequestVoteRequestAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6321_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6321_R1_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6321_R1_0_I2 /\ HandleRequestVoteResponseAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6321_R1_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6321_R1_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6321_R1_0_I2 /\ RejectAppendEntriesRequestAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6321_R1_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6321_R1_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6321_R1_0_I2
  \* (Inv6321_R1_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6321_R1_0_I2 /\ HandleAppendEntriesResponseAction => Inv6321_R1_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6321_R1_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv10_R2_0_I1
THEOREM L_4 == TypeOK /\ Inv6_R3_1_I1 /\ Inv10_R2_0_I1 /\ Next => Inv10_R2_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv10_R2_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv10_R2_0_I1 /\ RequestVoteAction => Inv10_R2_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv10_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv10_R2_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv10_R2_0_I1 /\ UpdateTermAction => Inv10_R2_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv10_R2_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
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
  <1>8. TypeOK /\ Inv6_R3_1_I1 /\ Inv10_R2_0_I1 /\ HandleRequestVoteResponseAction => Inv10_R2_0_I1'
       BY DEF TypeOK,Inv6_R3_1_I1,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv10_R2_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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


\*** Inv6_R3_1_I1
THEOREM L_5 == TypeOK /\ Inv6_R3_1_I1 /\ Next => Inv6_R3_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6_R3_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R3_1_I1 /\ RequestVoteAction => Inv6_R3_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6_R3_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R3_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv6_R3_1_I1 /\ UpdateTermAction => Inv6_R3_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6_R3_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6_R3_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6_R3_1_I1 /\ BecomeLeaderAction => Inv6_R3_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv6_R3_1_I1 /\ ClientRequestAction => Inv6_R3_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6_R3_1_I1 /\ AdvanceCommitIndexAction => Inv6_R3_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6_R3_1_I1 /\ AppendEntriesAction => Inv6_R3_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6_R3_1_I1 /\ HandleRequestVoteRequestAction => Inv6_R3_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6_R3_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R3_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6_R3_1_I1 /\ HandleRequestVoteResponseAction => Inv6_R3_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6_R3_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6_R3_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6_R3_1_I1 /\ RejectAppendEntriesRequestAction => Inv6_R3_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6_R3_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv6_R3_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6_R3_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6_R3_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6_R3_1_I1
  \* (Inv6_R3_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6_R3_1_I1 /\ HandleAppendEntriesResponseAction => Inv6_R3_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6_R3_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1900_R1_1_I1
THEOREM L_6 == TypeOK /\ Inv6184_R3_0_I2 /\ Inv984_R3_1_I1 /\ Inv6_R3_1_I1 /\ Inv1209_R3_1_I1 /\ Inv1900_R1_1_I1 /\ Next => Inv1900_R1_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1900_R1_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv1900_R1_1_I1 /\ RequestVoteAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1900_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1900_R1_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1900_R1_1_I1 /\ UpdateTermAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1900_R1_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1900_R1_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6184_R3_0_I2 /\ Inv1900_R1_1_I1 /\ BecomeLeaderAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,Inv6184_R3_0_I2,BecomeLeaderAction,BecomeLeader,Inv1900_R1_1_I1
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
  <1>7. TypeOK /\ Inv984_R3_1_I1 /\ Inv6_R3_1_I1 /\ Inv1209_R3_1_I1 /\ Inv1900_R1_1_I1 /\ HandleRequestVoteRequestAction => Inv1900_R1_1_I1'
       BY DEF TypeOK,Inv984_R3_1_I1,Inv6_R3_1_I1,Inv1209_R3_1_I1,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1900_R1_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
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


\*** Inv6184_R3_0_I2
THEOREM L_7 == TypeOK /\ Inv6184_R3_0_I2 /\ Next => Inv6184_R3_0_I2'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv6184_R3_0_I2,RequestVoteAction)
  <1>1. TypeOK /\ Inv6184_R3_0_I2 /\ RequestVoteAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv6184_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6184_R3_0_I2,UpdateTermAction)
  <1>2. TypeOK /\ Inv6184_R3_0_I2 /\ UpdateTermAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv6184_R3_0_I2,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv6184_R3_0_I2,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv6184_R3_0_I2 /\ BecomeLeaderAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,ClientRequestAction)
  <1>4. TypeOK /\ Inv6184_R3_0_I2 /\ ClientRequestAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv6184_R3_0_I2 /\ AdvanceCommitIndexAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,AppendEntriesAction)
  <1>6. TypeOK /\ Inv6184_R3_0_I2 /\ AppendEntriesAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv6184_R3_0_I2 /\ HandleRequestVoteRequestAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv6184_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6184_R3_0_I2,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv6184_R3_0_I2 /\ HandleRequestVoteResponseAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv6184_R3_0_I2,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv6184_R3_0_I2,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv6184_R3_0_I2 /\ RejectAppendEntriesRequestAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv6184_R3_0_I2 /\ AcceptAppendEntriesRequestAppendAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv6184_R3_0_I2 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv6184_R3_0_I2
  \* (Inv6184_R3_0_I2,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv6184_R3_0_I2 /\ HandleAppendEntriesResponseAction => Inv6184_R3_0_I2'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv6184_R3_0_I2
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv984_R3_1_I1
THEOREM L_8 == TypeOK /\ Inv984_R3_1_I1 /\ Next => Inv984_R3_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv984_R3_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv984_R3_1_I1 /\ RequestVoteAction => Inv984_R3_1_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv984_R3_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv984_R3_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv984_R3_1_I1 /\ UpdateTermAction => Inv984_R3_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv984_R3_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv984_R3_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv984_R3_1_I1 /\ BecomeLeaderAction => Inv984_R3_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv984_R3_1_I1 /\ ClientRequestAction => Inv984_R3_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv984_R3_1_I1 /\ AdvanceCommitIndexAction => Inv984_R3_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv984_R3_1_I1 /\ AppendEntriesAction => Inv984_R3_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv984_R3_1_I1 /\ HandleRequestVoteRequestAction => Inv984_R3_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv984_R3_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv984_R3_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv984_R3_1_I1 /\ HandleRequestVoteResponseAction => Inv984_R3_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv984_R3_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv984_R3_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv984_R3_1_I1 /\ RejectAppendEntriesRequestAction => Inv984_R3_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv984_R3_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv984_R3_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv984_R3_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv984_R3_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv984_R3_1_I1
  \* (Inv984_R3_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv984_R3_1_I1 /\ HandleAppendEntriesResponseAction => Inv984_R3_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv984_R3_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1209_R3_1_I1
THEOREM L_9 == TypeOK /\ Inv6_R3_1_I1 /\ Inv0_R8_0_I1 /\ Inv1209_R3_1_I1 /\ Next => Inv1209_R3_1_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1209_R3_1_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv6_R3_1_I1 /\ Inv0_R8_0_I1 /\ Inv1209_R3_1_I1 /\ RequestVoteAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,Inv6_R3_1_I1,Inv0_R8_0_I1,RequestVoteAction,RequestVote,Inv1209_R3_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1209_R3_1_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv1209_R3_1_I1 /\ UpdateTermAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1209_R3_1_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1209_R3_1_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1209_R3_1_I1 /\ BecomeLeaderAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv1209_R3_1_I1 /\ ClientRequestAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1209_R3_1_I1 /\ AdvanceCommitIndexAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1209_R3_1_I1 /\ AppendEntriesAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1209_R3_1_I1 /\ HandleRequestVoteRequestAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1209_R3_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1209_R3_1_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1209_R3_1_I1 /\ HandleRequestVoteResponseAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1209_R3_1_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1209_R3_1_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1209_R3_1_I1 /\ RejectAppendEntriesRequestAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1209_R3_1_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1209_R3_1_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1209_R3_1_I1
  \* (Inv1209_R3_1_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1209_R3_1_I1 /\ HandleAppendEntriesResponseAction => Inv1209_R3_1_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1209_R3_1_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv0_R8_0_I1
THEOREM L_10 == TypeOK /\ Inv1_R9_0_I0 /\ Inv0_R8_0_I1 /\ Next => Inv0_R8_0_I1'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv0_R8_0_I1,RequestVoteAction)
  <1>1. TypeOK /\ Inv0_R8_0_I1 /\ RequestVoteAction => Inv0_R8_0_I1'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv0_R8_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R8_0_I1,UpdateTermAction)
  <1>2. TypeOK /\ Inv0_R8_0_I1 /\ UpdateTermAction => Inv0_R8_0_I1'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv0_R8_0_I1,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv0_R8_0_I1,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv0_R8_0_I1 /\ BecomeLeaderAction => Inv0_R8_0_I1'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,ClientRequestAction)
  <1>4. TypeOK /\ Inv0_R8_0_I1 /\ ClientRequestAction => Inv0_R8_0_I1'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv0_R8_0_I1 /\ AdvanceCommitIndexAction => Inv0_R8_0_I1'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,AppendEntriesAction)
  <1>6. TypeOK /\ Inv0_R8_0_I1 /\ AppendEntriesAction => Inv0_R8_0_I1'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1_R9_0_I0 /\ Inv0_R8_0_I1 /\ HandleRequestVoteRequestAction => Inv0_R8_0_I1'
       BY DEF TypeOK,Inv1_R9_0_I0,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv0_R8_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R8_0_I1,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv0_R8_0_I1 /\ HandleRequestVoteResponseAction => Inv0_R8_0_I1'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv0_R8_0_I1,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv0_R8_0_I1,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv0_R8_0_I1 /\ RejectAppendEntriesRequestAction => Inv0_R8_0_I1'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv0_R8_0_I1 /\ AcceptAppendEntriesRequestAppendAction => Inv0_R8_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv0_R8_0_I1 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv0_R8_0_I1'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv0_R8_0_I1
  \* (Inv0_R8_0_I1,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv0_R8_0_I1 /\ HandleAppendEntriesResponseAction => Inv0_R8_0_I1'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv0_R8_0_I1
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next


\*** Inv1_R9_0_I0
THEOREM L_11 == TypeOK /\ Inv1_R9_0_I0 /\ Next => Inv1_R9_0_I0'
  <1>. USE A0,A1,A2,A3,A4,A5,A6,A7
  \* (Inv1_R9_0_I0,RequestVoteAction)
  <1>1. TypeOK /\ Inv1_R9_0_I0 /\ RequestVoteAction => Inv1_R9_0_I0'
       BY DEF TypeOK,RequestVoteAction,RequestVote,Inv1_R9_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R9_0_I0,UpdateTermAction)
  <1>2. TypeOK /\ Inv1_R9_0_I0 /\ UpdateTermAction => Inv1_R9_0_I0'
       BY DEF TypeOK,UpdateTermAction,UpdateTerm,Inv1_R9_0_I0,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero,AppendEntriesRequestType,AppendEntriesResponseType
  \* (Inv1_R9_0_I0,BecomeLeaderAction)
  <1>3. TypeOK /\ Inv1_R9_0_I0 /\ BecomeLeaderAction => Inv1_R9_0_I0'
       BY DEF TypeOK,BecomeLeaderAction,BecomeLeader,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,ClientRequestAction)
  <1>4. TypeOK /\ Inv1_R9_0_I0 /\ ClientRequestAction => Inv1_R9_0_I0'
       BY DEF TypeOK,ClientRequestAction,ClientRequest,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,AdvanceCommitIndexAction)
  <1>5. TypeOK /\ Inv1_R9_0_I0 /\ AdvanceCommitIndexAction => Inv1_R9_0_I0'
       BY DEF TypeOK,AdvanceCommitIndexAction,AdvanceCommitIndex,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,AppendEntriesAction)
  <1>6. TypeOK /\ Inv1_R9_0_I0 /\ AppendEntriesAction => Inv1_R9_0_I0'
       BY DEF TypeOK,AppendEntriesAction,AppendEntries,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,HandleRequestVoteRequestAction)
  <1>7. TypeOK /\ Inv1_R9_0_I0 /\ HandleRequestVoteRequestAction => Inv1_R9_0_I0'
       BY DEF TypeOK,HandleRequestVoteRequestAction,HandleRequestVoteRequest,Inv1_R9_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R9_0_I0,HandleRequestVoteResponseAction)
  <1>8. TypeOK /\ Inv1_R9_0_I0 /\ HandleRequestVoteResponseAction => Inv1_R9_0_I0'
       BY DEF TypeOK,HandleRequestVoteResponseAction,HandleRequestVoteResponse,Inv1_R9_0_I0,LastTerm,RequestVoteRequestType,RequestVoteResponseType,Terms,LogIndicesWithZero
  \* (Inv1_R9_0_I0,RejectAppendEntriesRequestAction)
  <1>9. TypeOK /\ Inv1_R9_0_I0 /\ RejectAppendEntriesRequestAction => Inv1_R9_0_I0'
       BY DEF TypeOK,RejectAppendEntriesRequestAction,RejectAppendEntriesRequest,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,AcceptAppendEntriesRequestAppendAction)
  <1>10. TypeOK /\ Inv1_R9_0_I0 /\ AcceptAppendEntriesRequestAppendAction => Inv1_R9_0_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestAppendAction,AcceptAppendEntriesRequestAppend,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,AcceptAppendEntriesRequestLearnCommitAction)
  <1>11. TypeOK /\ Inv1_R9_0_I0 /\ AcceptAppendEntriesRequestLearnCommitAction => Inv1_R9_0_I0'
       BY DEF TypeOK,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestLearnCommit,Inv1_R9_0_I0
  \* (Inv1_R9_0_I0,HandleAppendEntriesResponseAction)
  <1>12. TypeOK /\ Inv1_R9_0_I0 /\ HandleAppendEntriesResponseAction => Inv1_R9_0_I0'
       BY DEF TypeOK,HandleAppendEntriesResponseAction,HandleAppendEntriesResponse,Inv1_R9_0_I0
<1>13. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11,<1>12 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1> USE A0,A1,A2,A3,A4,A5,A6,A7
    <1>0. Init => TypeOK BY DEF Init, TypeOK, IndGlobal
    <1>1. Init => Safety BY DEF Init, Safety, IndGlobal, H_OnePrimaryPerTerm
    <1>2. Init => Inv8807_R0_0_I2 BY DEF Init, Inv8807_R0_0_I2, IndGlobal
    <1>3. Init => Inv6321_R1_0_I2 BY DEF Init, Inv6321_R1_0_I2, IndGlobal
    <1>4. Init => Inv10_R2_0_I1 BY DEF Init, Inv10_R2_0_I1, IndGlobal
    <1>5. Init => Inv6_R3_1_I1 BY DEF Init, Inv6_R3_1_I1, IndGlobal
    <1>6. Init => Inv1900_R1_1_I1 BY DEF Init, Inv1900_R1_1_I1, IndGlobal
    <1>7. Init => Inv6184_R3_0_I2 BY DEF Init, Inv6184_R3_0_I2, IndGlobal
    <1>8. Init => Inv984_R3_1_I1 BY DEF Init, Inv984_R3_1_I1, IndGlobal
    <1>9. Init => Inv1209_R3_1_I1 BY DEF Init, Inv1209_R3_1_I1, IndGlobal
    <1>10. Init => Inv0_R8_0_I1 BY DEF Init, Inv0_R8_0_I1, IndGlobal
    <1>11. Init => Inv1_R9_0_I0 BY DEF Init, Inv1_R9_0_I0, IndGlobal
    <1>a. QED BY <1>0,<1>1,<1>2,<1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,<1>10,<1>11 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10,L_11 DEF Next, IndGlobal

====