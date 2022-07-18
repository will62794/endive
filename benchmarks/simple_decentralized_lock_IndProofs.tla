---- MODULE simple_decentralized_lock_IndProofs ----
EXTENDS simple_decentralized_lock, FiniteSetTheorems

\* endive.py stats
\* -----------------
\* date: 2022-08-03T00:08:27.264494
\* is_inductive: True
\* inv_size: 4
\* invcheck_duration_secs: 6.678245782852173
\* ctielimcheck_duration_secs: 17.967918634414673
\* ctigen_duration_secs: 8.398974895477295
\* total_duration_secs: 33.082804918289185
\* total_num_ctis_eliminated: 2035
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 1674
\* total_num_invs_checked: 8144
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: True
\* tlc_workers: 8
\* seed: 10
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java -Xss16M
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv531_1_0_def == (has_lock = {}) \/ ((message = {}))
Inv4437_2_1_def == \A VARS \in Node : \A VART \in Node : \A VARU \in Node : \A VARV \in Node : (VARS=VART /\ message=message) \/ (~(<<VARS,VARU>> \in message) \/ (~(<<VART,VARV>> \in message)))
Inv4494_2_2_def == \A VARS \in Node : \A VART \in Node : \A VARU \in Node : (VARS=VART /\ message=message) \/ (~(<<VARU,VARS>> \in message) \/ (~(<<VARU,VART>> \in message)))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv531_1_0_def
  /\ Inv4437_2_1_def
  /\ Inv4494_2_2_def
  
ASSUME NodeFin == IsFiniteSet(Node)

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def
  <1>2. Inv
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def
  <1>3. Inv531_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def
  <1>4. Inv4437_2_1_def
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def
  <1>5. Inv4494_2_2_def
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
  <1>2. Inv'
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
  <1>3. Inv531_1_0_def'
    <2>1. CASE \E src,dst \in Node : Send(src,dst)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
    <2>2. CASE \E src,dst \in Node : Recv(src,dst)
      BY NodeFin, <2>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  <1>4. Inv4437_2_1_def'
    BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
  <1>5. Inv4494_2_2_def'
    <2>1. CASE \E src,dst \in Node : Send(src,dst)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
    <2>2. CASE \E src,dst \in Node : Recv(src,dst)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv531_1_0_def,Inv4437_2_1_def,Inv4494_2_2_def,Send,Recv
    <2>3. QED
      BY <2>1, <2>2 DEF Next
    
  <1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF IndAuto
 
====
