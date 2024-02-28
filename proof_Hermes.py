from proofs import *

#
# Hermes proof structure.
#

H_Inv18_1_0 = StructuredProofNode("LInv18_1_0", "H_Inv18_1_0")
H_Inv2558_2_1 = StructuredProofNode("LInv2558_2_1", "H_Inv2558_2_1")
H_Inv2587_2_2 = StructuredProofNode("LInv2587_2_2", "H_Inv2587_2_2")

hermes_root = StructuredProofNode("Safety", "HConsistent", children = {
    "HRcvValAction": [
        H_Inv18_1_0,
        H_Inv2558_2_1,
        H_Inv2587_2_2
        # rMCommittedImpliesOtherRMsPreparedOrCommitted
        # tMKnowsPrepareImpliesRMPreparedCommittedOrAborted,
        # commitMsgImpliesAllPrepared,
        # rMSentPrepareImpliesNotWorking,
        # committedRMImpliesCommitMsg,
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