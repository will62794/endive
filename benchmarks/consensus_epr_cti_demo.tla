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
    /\ H_LeaderImpliesVotesInQuorum

Ind2 ==
    /\ TypeOK
    /\ H_NoConflictingValues
    /\ H_UniqueLeaders
    /\ H_LeaderImpliesVotesInQuorum
    /\ H_DecidedImpliesLeader


Ind0_Constraint == TLCGet("level") = 1 => Ind0 
Ind1_Constraint == TLCGet("level") = 1 => Ind1 
Ind2_Constraint == TLCGet("level") = 1 => Ind2 
NextBounded ==  TLCGet("level") < 1 /\ Next

====