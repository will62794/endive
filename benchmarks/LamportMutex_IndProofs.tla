--------------------------- MODULE LamportMutex_IndProofs ----------------------------
(***************************************************************************)
(* TLA+ specification of Lamport's distributed mutual-exclusion algorithm  *)
(* that appeared as an example in                                          *)
(* L. Lamport:  Time, Clocks and the Ordering of Events in a Distributed   *)
(* System. CACM 21(7):558-565, 1978.                                       *)
(***************************************************************************)
EXTENDS LamportMutex, FiniteSets, SequenceTheorems, TLAPS


\* DISCOVERY 2024.


\* Proof Graph Stats
\* ==================
\* num proof graph nodes: 10
\* num proof obligations: 60
Safety == Mutex
Inv364_R0_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(VARI \in ack[VARJ]) \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv186_R0_0_I1 == \A VARI \in Proc : (ack[VARI] = Proc) \/ (~(VARI \in crit))
Inv165_R0_0_I1 == \A VARI \in Proc : (\A VOTHER \in Proc \ {VARI} : beats(VARI,VOTHER) /\ req = req) \/ (~(VARI \in crit))
Inv1320_R1_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : ~(network[VARI][VARJ] # <<>> /\ Head(network[VARI][VARJ]).type = "ack") \/ (~(req[VARI][VARJ] > req[VARJ][VARJ]))
Inv914_R1_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : \A VARRINDI \in DOMAIN network[VARI][VARJ] : (req[VARI][VARI] = network[VARI][VARJ][VARRINDI].clock) \/ (~(network[VARI][VARJ][VARRINDI].type = "req"))
Inv277_R2_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARJ \in crit))
Inv603_R4_2_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] = 0) \/ (~(network[VARJ][VARI] # <<>> /\ req[VARI][VARJ] = Head(network[VARJ][VARI]).clock))
Inv275_R6_0_I1 == \A VARI \in Proc : \A VARJ \in Proc : (req[VARI][VARJ] > 0) \/ (~(VARI \in ack[VARJ]))
Inv39_R8_1_I1 == \A VARI \in Proc : \A VARJ \in Proc : (VARI # VARJ /\ ack = ack) \/ (~(network[VARI][VARJ] # <<>>))

IndGlobal == 
  /\ TypeOK
  /\ Safety
  /\ Inv364_R0_0_I1
  /\ Inv1320_R1_0_I1
  /\ Inv914_R1_1_I1
  /\ Inv165_R0_0_I1
  /\ Inv277_R2_0_I1
  /\ Inv275_R6_0_I1
  /\ Inv39_R8_1_I1
  /\ Inv603_R4_2_I1
  /\ Inv186_R0_0_I1
  
Contains(s,mtype) == \E i \in 1 .. Len(s) : s[i].type = mtype
AtMostOne(s,mtype) == \A i,j \in 1 .. Len(s) :
  s[i].type = mtype /\ s[j].type = mtype => i = j
Precedes(s,mt1,mt2) == \A i,j \in 1 .. Len(s) :
  s[i].type = mt1 /\ s[j].type = mt2 => i < j

LEMMA NotContainsAtMostOne ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s,mtype)
  PROVE  AtMostOne(s, mtype)
BY DEF Contains, AtMostOne

LEMMA NotContainsPrecedes ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2, ~ Contains(s, mt2)
  PROVE  /\ Precedes(s, mt1, mt2)
         /\ Precedes(s, mt2, mt1)
BY DEF Contains, Precedes

LEMMA PrecedesHead ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         s # << >>,
         Precedes(s,mt1,mt2), Head(s).type = mt2
  PROVE  ~ Contains(s,mt1)
BY DEF Precedes, Contains

LEMMA AtMostOneTail ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         s # << >>, AtMostOne(s, mtype)
  PROVE  AtMostOne(Tail(s), mtype)
BY DEF AtMostOne

LEMMA ContainsTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mtype, AtMostOne(s, mtype)
  PROVE  Contains(Tail(s), mtype) <=> Contains(s, mtype) /\ Head(s).type # mtype
BY DEF Contains, AtMostOne

LEMMA AtMostOneHead ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         AtMostOne(s,mtype), s # << >>, Head(s).type = mtype
  PROVE  ~ Contains(Tail(s), mtype)
<1>. SUFFICES ASSUME NEW i \in 1 .. Len(Tail(s)), Tail(s)[i].type = mtype
              PROVE  FALSE
  BY Tail(s) \in Seq(Message), Isa DEF Contains
<1>. QED  BY HeadTailProperties DEF AtMostOne

LEMMA ContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, NEW m \in Message
  PROVE  Contains(Append(s,m), mtype) <=> m.type = mtype \/ Contains(s, mtype)
BY DEF Contains

LEMMA NotContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s, mtype), NEW m \in Message
  PROVE  /\ AtMostOne(Append(s,m), mtype)
         /\ m.type # mtype => ~ Contains(Append(s,m), mtype)
BY DEF Contains, AtMostOne

LEMMA AtMostOneSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, AtMostOne(s, mtype), 
         NEW m \in Message, m.type # mtype
  PROVE  AtMostOne(Append(s,m), mtype)
BY DEF AtMostOne

LEMMA PrecedesSend ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         NEW m \in Message, m.type # mt1
  PROVE  Precedes(Append(s,m), mt1, mt2) <=> Precedes(s, mt1, mt2)
BY DEF Precedes

LEMMA PrecedesTail ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2, Precedes(s, mt1, mt2)
  PROVE  Precedes(Tail(s), mt1, mt2)
BY DEF Precedes

LEMMA PrecedesInTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mt1, NEW mt2, mt1 # mt2,
         Head(s).type = mt1 \/ Head(s).type \notin {mt1, mt2},
         Precedes(Tail(s), mt1, mt2)
  PROVE  Precedes(s, mt1, mt2)
BY SMTT(30) DEF Precedes


\* mean in-degree: 1.1
\* median in-degree: 1
\* max in-degree: 3
\* min in-degree: 0
\* mean variable slice size: 0
USE DEF Clock

\*** TypeOK
THEOREM L_0 == TypeOK /\ TypeOK /\ Next => TypeOK'
  \* (TypeOK,RequestAction)
  <1>1. TypeOK /\ TypeOK /\ RequestAction => TypeOK'
       BY DEF TypeOK,RequestAction,Request,TypeOK
  \* (TypeOK,EnterAction)
  <1>2. TypeOK /\ TypeOK /\ EnterAction => TypeOK'
       BY DEF TypeOK,EnterAction,Enter,TypeOK
  \* (TypeOK,ExitAction)
  <1>3. TypeOK /\ TypeOK /\ ExitAction => TypeOK'
       BY DEF TypeOK,ExitAction,Exit,TypeOK
  \* (TypeOK,ReceiveRequestAction)
  <1>4. TypeOK /\ TypeOK /\ ReceiveRequestAction => TypeOK'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,TypeOK
  \* (TypeOK,ReceiveAckAction)
  <1>5. TypeOK /\ TypeOK /\ ReceiveAckAction => TypeOK'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,TypeOK
  \* (TypeOK,ReceiveReleaseAction)
  <1>6. TypeOK /\ TypeOK /\ ReceiveReleaseAction => TypeOK'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,TypeOK
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\* (ROOT SAFETY PROP)
\*** Safety
THEOREM L_1 == TypeOK /\ Safety /\ Next => Safety'
  \* (Safety,RequestAction)
  <1>1. TypeOK /\ Safety /\ RequestAction => Safety'
       BY DEF TypeOK,RequestAction,Request,Safety,Mutex
  \* (Safety,EnterAction)
  <1>2. TypeOK /\ Safety /\ EnterAction => Safety'
       BY DEF TypeOK,EnterAction,Enter,Safety,Mutex,Message,AckMessage,RelMessage,beats,ReqMessage
  \* (Safety,ExitAction)
  <1>3. TypeOK /\ Safety /\ ExitAction => Safety'
       BY DEF TypeOK,ExitAction,Exit,Safety,Mutex
  \* (Safety,ReceiveRequestAction)
  <1>4. TypeOK /\ Safety /\ ReceiveRequestAction => Safety'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Safety,Mutex
  \* (Safety,ReceiveAckAction)
  <1>5. TypeOK /\ Safety /\ ReceiveAckAction => Safety'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Safety,Mutex
  \* (Safety,ReceiveReleaseAction)
  <1>6. TypeOK /\ Safety /\ ReceiveReleaseAction => Safety'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Safety,Mutex
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv364_R0_0_I1
THEOREM L_2 == TypeOK /\ Inv364_R0_0_I1 /\ Next => Inv364_R0_0_I1'
  \* (Inv364_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv364_R0_0_I1 /\ RequestAction => Inv364_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv364_R0_0_I1 /\ EnterAction => Inv364_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv364_R0_0_I1 /\ ExitAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv364_R0_0_I1 /\ ReceiveRequestAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv364_R0_0_I1 /\ ReceiveAckAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv364_R0_0_I1
  \* (Inv364_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv364_R0_0_I1 /\ ReceiveReleaseAction => Inv364_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv364_R0_0_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv1320_R1_0_I1
THEOREM L_3 == TypeOK /\ Inv1320_R1_0_I1 /\ Next => Inv1320_R1_0_I1'
  \* (Inv1320_R1_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv1320_R1_0_I1 /\ RequestAction => Inv1320_R1_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv1320_R1_0_I1
  \* (Inv1320_R1_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv1320_R1_0_I1 /\ EnterAction => Inv1320_R1_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv1320_R1_0_I1
  \* (Inv1320_R1_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv1320_R1_0_I1 /\ ExitAction => Inv1320_R1_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv1320_R1_0_I1
  \* (Inv1320_R1_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv1320_R1_0_I1 /\ ReceiveRequestAction => Inv1320_R1_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv1320_R1_0_I1
  \* (Inv1320_R1_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv1320_R1_0_I1 /\ ReceiveAckAction => Inv1320_R1_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv1320_R1_0_I1
  \* (Inv1320_R1_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv1320_R1_0_I1 /\ ReceiveReleaseAction => Inv1320_R1_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv1320_R1_0_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv914_R1_1_I1
THEOREM L_4 == TypeOK /\ Inv914_R1_1_I1 /\ Next => Inv914_R1_1_I1'
  \* (Inv914_R1_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv914_R1_1_I1 /\ RequestAction => Inv914_R1_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv914_R1_1_I1
  \* (Inv914_R1_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv914_R1_1_I1 /\ EnterAction => Inv914_R1_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv914_R1_1_I1
  \* (Inv914_R1_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv914_R1_1_I1 /\ ExitAction => Inv914_R1_1_I1'
       BY HeadTailProperties DEF TypeOK,ExitAction,Exit,Inv914_R1_1_I1,Broadcast,RelMessage
  \* (Inv914_R1_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv914_R1_1_I1 /\ ReceiveRequestAction => Inv914_R1_1_I1'
       BY HeadTailProperties DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv914_R1_1_I1
  \* (Inv914_R1_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv914_R1_1_I1 /\ ReceiveAckAction => Inv914_R1_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv914_R1_1_I1
  \* (Inv914_R1_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv914_R1_1_I1 /\ ReceiveReleaseAction => Inv914_R1_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv914_R1_1_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv165_R0_0_I1
THEOREM L_5 == TypeOK /\ Inv165_R0_0_I1 /\ Next => Inv165_R0_0_I1'
  \* (Inv165_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv165_R0_0_I1 /\ RequestAction => Inv165_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv165_R0_0_I1
  \* (Inv165_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv165_R0_0_I1 /\ EnterAction => Inv165_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv165_R0_0_I1,beats
  \* (Inv165_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv165_R0_0_I1 /\ ExitAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv165_R0_0_I1,beats,Broadcast
  \* (Inv165_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv165_R0_0_I1 /\ ReceiveRequestAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv165_R0_0_I1,beats
  \* (Inv165_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv165_R0_0_I1 /\ ReceiveAckAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv165_R0_0_I1,beats
  \* (Inv165_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv165_R0_0_I1 /\ ReceiveReleaseAction => Inv165_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv165_R0_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv277_R2_0_I1
THEOREM L_6 == TypeOK /\ Inv277_R2_0_I1 /\ Next => Inv277_R2_0_I1'
  \* (Inv277_R2_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv277_R2_0_I1 /\ RequestAction => Inv277_R2_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv277_R2_0_I1
  \* (Inv277_R2_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv277_R2_0_I1 /\ EnterAction => Inv277_R2_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv277_R2_0_I1
  \* (Inv277_R2_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv277_R2_0_I1 /\ ExitAction => Inv277_R2_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv277_R2_0_I1
  \* (Inv277_R2_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv277_R2_0_I1 /\ ReceiveRequestAction => Inv277_R2_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv277_R2_0_I1,beats,AckMessage
  \* (Inv277_R2_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv277_R2_0_I1 /\ ReceiveAckAction => Inv277_R2_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv277_R2_0_I1
  \* (Inv277_R2_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv277_R2_0_I1 /\ ReceiveReleaseAction => Inv277_R2_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv277_R2_0_I1,beats
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next

ASSUME A == IsFiniteSet(Proc)
\*** Inv275_R6_0_I1
THEOREM L_7 == TypeOK /\ Inv275_R6_0_I1 /\ Next => Inv275_R6_0_I1'
  \* (Inv275_R6_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv275_R6_0_I1 /\ RequestAction => Inv275_R6_0_I1'
       BY A DEF TypeOK,RequestAction,Request,Inv275_R6_0_I1,Broadcast,ReqMessage
  \* (Inv275_R6_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv275_R6_0_I1 /\ EnterAction => Inv275_R6_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv275_R6_0_I1
  \* (Inv275_R6_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv275_R6_0_I1 /\ ExitAction => Inv275_R6_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv275_R6_0_I1
  \* (Inv275_R6_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv275_R6_0_I1 /\ ReceiveRequestAction => Inv275_R6_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv275_R6_0_I1
  \* (Inv275_R6_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv275_R6_0_I1 /\ ReceiveAckAction => Inv275_R6_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv275_R6_0_I1
  \* (Inv275_R6_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv275_R6_0_I1 /\ ReceiveReleaseAction => Inv275_R6_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv275_R6_0_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv39_R8_1_I1
THEOREM L_8 == TypeOK /\ Inv39_R8_1_I1 /\ Next => Inv39_R8_1_I1'
  \* (Inv39_R8_1_I1,RequestAction)
  <1>1. TypeOK /\ Inv39_R8_1_I1 /\ RequestAction => Inv39_R8_1_I1'
       BY DEF TypeOK,RequestAction,Request,Inv39_R8_1_I1
  \* (Inv39_R8_1_I1,EnterAction)
  <1>2. TypeOK /\ Inv39_R8_1_I1 /\ EnterAction => Inv39_R8_1_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv39_R8_1_I1
  \* (Inv39_R8_1_I1,ExitAction)
  <1>3. TypeOK /\ Inv39_R8_1_I1 /\ ExitAction => Inv39_R8_1_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv39_R8_1_I1
  \* (Inv39_R8_1_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv39_R8_1_I1 /\ ReceiveRequestAction => Inv39_R8_1_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv39_R8_1_I1
  \* (Inv39_R8_1_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv39_R8_1_I1 /\ ReceiveAckAction => Inv39_R8_1_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv39_R8_1_I1
  \* (Inv39_R8_1_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv39_R8_1_I1 /\ ReceiveReleaseAction => Inv39_R8_1_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv39_R8_1_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv603_R4_2_I1
THEOREM L_9 == TypeOK /\ Inv603_R4_2_I1 /\ Next => Inv603_R4_2_I1'
  \* (Inv603_R4_2_I1,RequestAction)
  <1>1. TypeOK /\ Inv603_R4_2_I1 /\ RequestAction => Inv603_R4_2_I1'
       BY DEF TypeOK,RequestAction,Request,Inv603_R4_2_I1,Broadcast
  \* (Inv603_R4_2_I1,EnterAction)
  <1>2. TypeOK /\ Inv603_R4_2_I1 /\ EnterAction => Inv603_R4_2_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv603_R4_2_I1
  \* (Inv603_R4_2_I1,ExitAction)
  <1>3. TypeOK /\ Inv603_R4_2_I1 /\ ExitAction => Inv603_R4_2_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv603_R4_2_I1
  \* (Inv603_R4_2_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv603_R4_2_I1 /\ ReceiveRequestAction => Inv603_R4_2_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv603_R4_2_I1
  \* (Inv603_R4_2_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv603_R4_2_I1 /\ ReceiveAckAction => Inv603_R4_2_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv603_R4_2_I1
  \* (Inv603_R4_2_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv603_R4_2_I1 /\ ReceiveReleaseAction => Inv603_R4_2_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv603_R4_2_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


\*** Inv186_R0_0_I1
THEOREM L_10 == TypeOK /\ Inv186_R0_0_I1 /\ Next => Inv186_R0_0_I1'
  \* (Inv186_R0_0_I1,RequestAction)
  <1>1. TypeOK /\ Inv186_R0_0_I1 /\ RequestAction => Inv186_R0_0_I1'
       BY DEF TypeOK,RequestAction,Request,Inv186_R0_0_I1,Broadcast,ReqMessage
  \* (Inv186_R0_0_I1,EnterAction)
  <1>2. TypeOK /\ Inv186_R0_0_I1 /\ EnterAction => Inv186_R0_0_I1'
       BY DEF TypeOK,EnterAction,Enter,Inv186_R0_0_I1
  \* (Inv186_R0_0_I1,ExitAction)
  <1>3. TypeOK /\ Inv186_R0_0_I1 /\ ExitAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ExitAction,Exit,Inv186_R0_0_I1
  \* (Inv186_R0_0_I1,ReceiveRequestAction)
  <1>4. TypeOK /\ Inv186_R0_0_I1 /\ ReceiveRequestAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ReceiveRequestAction,ReceiveRequest,Inv186_R0_0_I1
  \* (Inv186_R0_0_I1,ReceiveAckAction)
  <1>5. TypeOK /\ Inv186_R0_0_I1 /\ ReceiveAckAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ReceiveAckAction,ReceiveAck,Inv186_R0_0_I1
  \* (Inv186_R0_0_I1,ReceiveReleaseAction)
  <1>6. TypeOK /\ Inv186_R0_0_I1 /\ ReceiveReleaseAction => Inv186_R0_0_I1'
       BY DEF TypeOK,ReceiveReleaseAction,ReceiveRelease,Inv186_R0_0_I1
<1>7. QED BY <1>1,<1>2,<1>3,<1>4,<1>5,<1>6 DEF Next


THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0,L_1,L_2,L_3,L_4,L_5,L_6,L_7,L_8,L_9,L_10 DEF Next, IndGlobal


==============================================================================
==============================================================================