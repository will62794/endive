from proofs import *

#
# Hermes proof structure.
#

H_Inv18_1_0 = StructuredProofNode("LInv18_1_0", "H_Inv18_1_0")
H_Inv2558_2_1 = StructuredProofNode("LInv2558_2_1", "H_Inv2558_2_1")
H_Inv2587_2_2 = StructuredProofNode("LInv2587_2_2", "H_Inv2587_2_2")

H_Inv130_R0_1_0 = StructuredProofNode("LInv130_R0_1_0", "H_Inv130_R0_1_0")
H_Inv3149_R0_2_1 = StructuredProofNode("LInv3149_R0_2_1", "H_Inv3149_R0_2_1")
H_Inv545_R0_2_2 = StructuredProofNode("LInv545_R0_2_2", "H_Inv545_R0_2_2")
H_Inv3135_R0_2_3 = StructuredProofNode("LInv3135_R0_2_3", "H_Inv3135_R0_2_3")
H_Inv548_R0_2_4 = StructuredProofNode("LInv548_R0_2_4", "H_Inv548_R0_2_4")

hermes_root = StructuredProofNode("Safety", "HConsistent", children = {
    "HRcvValAction": [
        # H_Inv130_R0_1_0,
        # H_Inv3149_R0_2_1,
        # H_Inv545_R0_2_2,
        # H_Inv3135_R0_2_3,
        # H_Inv548_R0_2_4
        # rMCommittedImpliesOtherRMsPreparedOrCommitted
        # tMKnowsPrepareImpliesRMPreparedCommittedOrAborted,
        # commitMsgImpliesAllPrepared,
        # rMSentPrepareImpliesNotWorking,
        # committedRMImpliesCommitMsg,
    ],
    "HSendValsAction": [
        # H_Inv130_R0_1_0,
        # H_Inv3149_R0_2_1,
        # H_Inv545_R0_2_2,
        # H_Inv3135_R0_2_3,
        # H_Inv548_R0_2_4
    ]
})

root = hermes_root
actions = [
    "RcvInvAction",
    "FollowerWriteReplayAction",
    "RcvValAction",
    "ReadAction",
    "CoordWriteReplayAction",
    "WriteAction",
    "RcvAckAction",
    "SendValsAction",
    "NodeFailureAction"
]
nodes = []