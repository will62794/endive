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

VALMsgImpliesValidAliveNodesHaveEqualOrNewer = StructuredProofNode("VALMsgImpliesValidAliveNodesHaveEqualOrNewer", "H_VALMsgImpliesValidAliveNodesHaveEqualOrNewer") 

HBD = StructuredProofNode("HBDnode", "HBD")

H_VALMsgImpliesSomeValidNodeWithVersion = StructuredProofNode("VALMsgImpliesSomeValidNodeWithVersion", "H_VALMsgImpliesSomeValidNodeWithVersion")
H_VALMsgImpliesInvalidAliveNodesHaveEqualOrNewer = StructuredProofNode("VALMsgImpliesInvalidAliveNodesHaveEqualOrNewer", "H_VALMsgImpliesInvalidAliveNodesHaveEqualOrNewer")

H_ACKImpliesFreshTS = StructuredProofNode("ACKImpliesFreshTS", "H_ACKImpliesFreshTS")

hermes_root = StructuredProofNode("Safety", "HConsistent", children = {
    "HRcvValAction": [
        # HBD,
        VALMsgImpliesValidAliveNodesHaveEqualOrNewer,
        H_VALMsgImpliesSomeValidNodeWithVersion,
    ],
    "HSendValsAction": [
        H_ACKImpliesFreshTS
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