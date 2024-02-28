from proofs import *

#
# Hermes proof structure.
#

hermes_root = StructuredProofNode("Safety", "HConsistent", children = {
    "HRcvValAction": [
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