---- MODULE consensus_epr_cti_demo ----
EXTENDS consensus_epr

Ind0 ==
    /\ TypeOK
    /\ H_NoConflictingValues
    /\ H_UniqueLeaders

Ind1 ==
    /\ TypeOK
    /\ H_NoConflictingValues
    /\ H_UniqueLeaders
    /\ H_LeaderHasQuorum

Ind2 ==
    /\ TypeOK
    /\ H_NoConflictingValues
    /\ H_UniqueLeaders
    /\ H_LeaderHasQuorum
    /\ H_DecidedImpliesLeader


Ind0_Constraint == TLCGet("level") = 1 => Ind0 
H_UniqueLeaders_Constraint == TLCGet("level") = 1 => H_UniqueLeaders 
Ind1_Constraint == TLCGet("level") = 1 => Ind1 
Ind2_Constraint == TLCGet("level") = 1 => Ind2 
NextBounded ==  TLCGet("level") < 1 /\ Next

====