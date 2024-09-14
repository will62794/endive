------------- MODULE Paxos_IndProofs ----
EXTENDS Paxos, TLAPS

\* Proof Graph Stats
\* ==================
\* seed: 111115
\* num proof graph nodes: 1
\* num proof obligations: 5
Safety == Inv
Inv500_afae_R0_0_I2 == \A VALI \in Value : \A BALI \in Ballot : (VALI \in chosen) \/ (~(ChosenAt(BALI, VALI) /\ msgs2b = msgs2b)) \/ ((chosen = {}))
Inv1519_e18f_R0_0_I2 == \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : (VALI=VALJ /\ msgs2b = msgs2b) \/ (~(ChosenAt(BALJ, VALJ) /\ msgs2b = msgs2b)) \/ (~(ChosenAt(BALI, VALI) /\ msgs2b = msgs2b))

IndGlobal == 
  /\ TypeOK
  /\ Inv1519_e18f_R0_0_I2


\* mean in-degree: 0.0
\* median in-degree: 0
\* max in-degree: 0
\* min in-degree: 0
\* mean variable slice size: 0


\* (ROOT SAFETY PROP)
\*** Inv1519_e18f_R0_0_I2
THEOREM L_0 == TypeOK /\ Inv1519_e18f_R0_0_I2 /\ Next => Inv1519_e18f_R0_0_I2'
  \* (Inv1519_e18f_R0_0_I2,Phase1aAction)
  <1>1. TypeOK  /\ Phase1aAction => Inv1519_e18f_R0_0_I2' BY DEF TypeOK,Inv1519_e18f_R0_0_I2, ChosenAt
  \* (Inv1519_e18f_R0_0_I2,Phase2aAction)
  <1>2.  Inv1519_e18f_R0_0_I2 /\ Phase2aAction => Inv1519_e18f_R0_0_I2' BY DEF TypeOK,Phase2aAction,Inv1519_e18f_R0_0_I2
  \* (Inv1519_e18f_R0_0_I2,Phase1bAction)
  <1>3. TypeOK /\ Inv1519_e18f_R0_0_I2 /\ Phase1bAction => Inv1519_e18f_R0_0_I2' BY DEF TypeOK,Phase1bAction,Phase1b,Inv1519_e18f_R0_0_I2
  \* (Inv1519_e18f_R0_0_I2,Phase2bAction)
  <1>4. TypeOK /\ Inv1519_e18f_R0_0_I2 /\ Phase2bAction => Inv1519_e18f_R0_0_I2' BY DEF TypeOK,Phase2bAction,Phase2b,Inv1519_e18f_R0_0_I2
  \* (Inv1519_e18f_R0_0_I2,LearnAction)
  <1>5. TypeOK /\ Inv1519_e18f_R0_0_I2 /\ LearnAction => Inv1519_e18f_R0_0_I2' BY DEF TypeOK,LearnAction,Learn,Inv1519_e18f_R0_0_I2
<1>6. QED BY <1>1,<1>2,<1>3,<1>4,<1>5 DEF Next

\* Initiation.
THEOREM Init => IndGlobal
    <1>0. Init => Inv1519_e18f_R0_0_I2 BY DEF Init, Inv1519_e18f_R0_0_I2, IndGlobal
    <1>a. QED BY <1>0 DEF IndGlobal

\* Consecution.
THEOREM IndGlobal /\ Next => IndGlobal'
  BY L_0 DEF Next, IndGlobal

======