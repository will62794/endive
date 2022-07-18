---- MODULE firewall_IndProofs ----
EXTENDS firewall, FiniteSetTheorems

\* endive.py stats
\* -----------------
\* date: 2022-08-07T02:04:07.959284
\* is_inductive: True
\* inv_size: 5
\* invcheck_duration_secs: 5.875180006027222
\* ctielimcheck_duration_secs: 23.84526491165161
\* ctigen_duration_secs: 5.690789222717285
\* total_duration_secs: 35.51509404182434
\* total_num_ctis_eliminated: 1740
\* total_num_cti_elimination_rounds: 1
\* total_num_invs_generated: 2996
\* total_num_invs_checked: 4814
\* num_invs: 15000
\* num_iters: 3
\* num_round: 4
\* num_simulate_traces: 50000
\* opt_quant_minimize: False
\* tlc_workers: 6
\* seed: 10
\* os: posix
\* system: Darwin
\* java_exe: /Users/willyschultz/Downloads/zulu15.32.15-ca-jdk15.0.3-macosx_aarch64/bin/java
\* java_version_info: openjdk version "15.0.3" 2021-04-20 OpenJDK Runtime Environment Zulu15.32+15-CA (build 15.0.3+3) OpenJDK 64-Bit Server VM Zulu15.32+15-CA (build 15.0.3+3, mixed mode)
\* processor: arm
\* cpu_count: 8

\* Inductive strengthening conjuncts
Inv285_1_0_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : (internal[VARI]) \/ (~(VARJ \in sent[VARJ]))
Inv201_1_1_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : (VARJ \in sent[VARK]) \/ (~(VARJ \in allowed_in))
Inv370_1_2_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : ~(VARI \in allowed_in) \/ (~(internal[VARI]))
Inv3144_2_3_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : (internal[VARI]) \/ ((internal[VARJ])) \/ (~(VARI \in sent[VARJ]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv285_1_0_def
  /\ Inv201_1_1_def
  /\ Inv370_1_2_def
  /\ Inv3144_2_3_def

ASSUME NodeNonEmpty == Node # {}
ASSUME NodeFinite == IsFiniteSet(Node)

\* TLAPS Proof skeleton.
 THEOREM Init => IndAuto 
  BY DEF TypeOK,Init,Next,IndAuto,Inv,Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def
  
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto,
                      Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. CASE \E s,t \in Node : SendFromInternal(s,t)
    <2>1. TypeOK'
      BY <1>1 DEF TypeOK,Init,Next,IndAuto,Inv,Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def, SendFromInternal
      
    <2>2. Inv'
        <3>1. PICK a,b \in Node : SendFromInternal(a,b) BY <1>1
        <3>2. SUFFICES ASSUME NEW s \in Node,
                              NEW d \in Node,
                              d \in sent'[s],
                              internal'[d]
              PROVE \E i \in Node : internal'[i] /\ s \in sent'[i]
              BY DEF Inv
        <3>3. CASE b = s BY <3>1, <3>2, <3>3 DEF SendFromInternal, IndAuto, Inv, TypeOK
        <3>4. CASE b # s BY <3>1, <3>2, <3>4 DEF SendFromInternal, IndAuto, Inv, TypeOK
        <3>. QED BY <3>3, <3>4
        
    <2>3. Inv285_1_0_def'
        <3>1. PICK a,b \in Node : SendFromInternal(a,b) BY <1>1
        <3>2. SUFFICES \A VARI,VARJ \in Node : \E k \in Node : (internal'[VARJ]) \/ ~(VARI \in sent'[VARI])
            BY DEF Inv285_1_0_def
        <3>.  TAKE i,j \in Node
        <3>3. internal[j] \/ ~(i \in sent[i]) BY DEF IndAuto, Inv285_1_0_def
        <3>4. CASE internal[j] BY <3>1, <3>4 DEF SendFromInternal, IndAuto, TypeOK
        <3>5. CASE ~(i \in sent[i]) BY <3>1, <3>5 DEF SendFromInternal, IndAuto, TypeOK
        <3>. QED BY <3>3, <3>4, <3>5
      
    <2>4. Inv201_1_1_def'
        <3>1. PICK a,b \in Node : SendFromInternal(a,b) BY <1>1
        <3>2. SUFFICES \A VARI,VARJ \in Node : \E k \in Node : ~(VARI \in allowed_in') \/ (VARI \in sent'[k])
            BY DEF Inv201_1_1_def
        <3>.  TAKE i,j \in Node
        <3>3. PICK k \in Node : ~(i \in allowed_in) \/ (i \in sent[k]) BY DEF IndAuto, Inv201_1_1_def
        <3>4. CASE ~(i \in allowed_in) BY <3>1, <3>4 DEF SendFromInternal, IndAuto, TypeOK, Inv201_1_1_def
        <3>5. CASE (i \in sent[k]) BY <3>1, <3>5 DEF SendFromInternal, IndAuto, TypeOK, Inv201_1_1_def
        <3>. QED BY <3>3, <3>4, <3>5
    
    <2>5. Inv370_1_2_def'
      BY <1>1 DEF TypeOK,IndAuto,Inv,Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def, SendFromInternal
    <2>6. Inv3144_2_3_def'
      BY <1>1 DEF TypeOK,IndAuto,Inv3144_2_3_def, SendFromInternal
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF IndAuto
    
  <1>2. CASE \E s,t \in Node : SendToInternal(s,t)  
    <2>1. TypeOK'
      BY <1>2 DEF TypeOK,Init,Next,IndAuto,Inv,Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def,SendToInternal
    <2>2. Inv'
        <3>1. PICK a,b \in Node : SendToInternal(a,b) BY <1>2
        <3>2. SUFFICES ASSUME NEW s \in Node,
                              NEW d \in Node,
                              d \in sent'[s],
                              internal'[d]
              PROVE \E i \in Node : internal'[i] /\ s \in sent'[i]
              BY DEF Inv
        <3>3. CASE b = d
            <4>1. CASE a = s
                BY <3>1, <3>2, <3>3, <4>1 DEF SendToInternal, IndAuto, Inv, TypeOK, Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def
            <4>2. CASE a # s BY <3>1, <3>2, <3>3, <4>2 DEF SendToInternal, IndAuto, Inv, TypeOK
            <4>. QED BY <4>1, <4>2
        <3>4. CASE b # d BY <3>1, <3>2, <3>4 DEF SendToInternal, IndAuto, Inv, TypeOK
        <3>. QED BY <3>3, <3>4
        
    <2>3. Inv285_1_0_def'
        <3>1. PICK a,b \in Node : SendToInternal(a,b) BY <1>2
        <3>2. SUFFICES \A VARI,VARJ \in Node : \E k \in Node : (internal'[VARJ]) \/ ~(VARI \in sent'[VARI])
            BY DEF Inv285_1_0_def
        <3>.  TAKE i,j \in Node
        <3>3. internal[j] \/ ~(i \in sent[i]) BY DEF IndAuto, Inv285_1_0_def
        <3>4. CASE internal[j] BY <3>1, <3>4 DEF SendToInternal, IndAuto, TypeOK
        <3>5. CASE ~(i \in sent[i]) BY <3>1, <3>5 DEF SendToInternal, IndAuto, TypeOK
        <3>. QED BY <3>3, <3>4, <3>5
        
    <2>4. Inv201_1_1_def'
      BY <1>2 DEF TypeOK,IndAuto,Inv,Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def, SendToInternal
    <2>5. Inv370_1_2_def'
      BY <1>2 DEF TypeOK,IndAuto,Inv,Inv285_1_0_def,Inv201_1_1_def,Inv370_1_2_def,Inv3144_2_3_def, SendToInternal
      
    \* Inv3144_2_3_def == \A VARI,VARJ \in Node : \E k \in Node : (internal[VARI]) \/ ((internal[VARJ]) \/ (~(VARJ \in sent[VARI]) /\ (TRUE)))
    <2>6. Inv3144_2_3_def'
        <3>1. PICK a,b \in Node : SendToInternal(a,b) BY <1>2
        <3>2. SUFFICES \A VARI,VARJ \in Node : \E k \in Node : internal'[VARI] \/ internal'[VARJ] \/ ~(VARJ \in sent'[VARI])
            BY DEF Inv3144_2_3_def
        <3>.  TAKE i,j \in Node
        <3>3. PICK k \in Node : internal[i] \/ internal[j] \/ ~(j \in sent[i]) BY DEF IndAuto, Inv3144_2_3_def
        <3>4. CASE internal[i] BY <3>1, <3>4 DEF SendToInternal, IndAuto, TypeOK
        <3>5. CASE internal[j] BY <3>1, <3>5 DEF SendToInternal, IndAuto, TypeOK
        <3>6. CASE j \notin sent[i] BY <3>1, <3>6 DEF SendToInternal, IndAuto, TypeOK
        <3>. QED BY <3>3, <3>4, <3>5, <3>6
      
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF IndAuto
    
  <1>3. QED
    BY <1>1, <1>2 DEF Next
 
  

====
