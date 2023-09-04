from proofs import *

#
# TwoPhase proof structure.
#


tMKnowsPrepareImpliesRMSentPrepare = StructuredProofNode("TMKnowsPrepareImpliesRMSentPrepare", "H_TMKnowsPrepareImpliesRMSentPrepare")

######
######
## lemmaelim
# children = {
#     "TMAbort" : ""
#     "TMAbort" : StructuredProofNode("InitImpliesNoAbortMsg", "H_InitImpliesNoAbortMsg")
# }
commitMsgImpliesNoAbortMsg = StructuredProofNode("CommitMsgImpliesNoAbortMsg", "H_CommitMsgImpliesNoAbortMsg", children = {
    # lemmaTRUE,
    "TMAbort": [
        StructuredProofNode("InitImpliesNoCommitMsg", "H_InitImpliesNoCommitMsg")
    ],
    "TMCommit": [
        StructuredProofNode("InitImpliesNoAbortMsg", "H_InitImpliesNoAbortMsg")
    ]
})

rMSentPrepareImpliesNotWorking = StructuredProofNode("RMSentPrepareImpliesNotWorking", "H_RMSentPrepareImpliesNotWorking")

abortMsgSentImpliesTMAborted = StructuredProofNode("AbortMsgSentImpliesTMAborted", "H_AbortMsgSentImpliesTMAborted")

rMAbortAfterPrepareImpliesTMAborted = StructuredProofNode("RMAbortAfterPrepareImpliesTMAborted", "H_RMAbortAfterPrepareImpliesTMAborted", children = {
    "RMRcvAbortMsgAction": [
        abortMsgSentImpliesTMAborted
    ],
    "RMChooseToAbortAction": [
        rMSentPrepareImpliesNotWorking,
    ]
})

allPreparedImpliesAllPreparesSent = StructuredProofNode("AllPreparedImpliesAllPreparesSent", "H_AllPreparedImpliesAllPreparesSent", children = {
    "TMRcvPreparedAction": [tMKnowsPrepareImpliesRMSentPrepare]
})

commitMsgImpliesAllPreparesSent = StructuredProofNode("CommitMsgImpliesAllPreparesSent", "H_CommitMsgImpliesAllPreparesSent", children={
    "TMCommit": [tMKnowsPrepareImpliesRMSentPrepare]
})


commitMsgImpliesNoRMAborted = StructuredProofNode("CommitMsgImpliesNoRMAborted", "H_CommitMsgImpliesNoRMAborted", children = {
    "RMRcvAbortMsgAction": [
        commitMsgImpliesAllPreparesSent,
        commitMsgImpliesNoAbortMsg
    ],
    "RMChooseToAbortAction": [
        rMSentPrepareImpliesNotWorking,
        commitMsgImpliesAllPreparesSent
    ],
    "TMCommit": [
        allPreparedImpliesAllPreparesSent,
        rMAbortAfterPrepareImpliesTMAborted
    ]
    
})

tMKnowsPrepareImpliesRMPreparedCommittedOrAborted = StructuredProofNode(
    "TMKnowsPrepareImpliesRMPreparedCommittedOrAborted", 
    "H_TMKnowsPrepareImpliesRMPreparedCommittedOrAborted", children = {
        # lemmaTRUE,
        "TMRcvPreparedAction": [rMSentPrepareImpliesNotWorking]
})

commitMsgImpliesAllPrepared = StructuredProofNode("CommitMsgImpliesAllPrepared", "H_CommitMsgImpliesAllPrepared")

committedRMImpliesCommitMsg = StructuredProofNode("CommittedRMImpliesCommitMsg", "H_CommittedRMImpliesCommitMsg")

# TwoPhase proof structure.
# twopc_children = [
#     StructuredProofNode("CommitMsgImpliesAllPrepared", "H_CommitMsgImpliesAllPrepared", parent_action="RMChooseToAbortAction"),
#     commitMsgImpliesNoAbortMsg,
#     commitMsgImpliesNoRMAborted,
#     committedRMImpliesCommitMsg,
#     tMKnowsPrepareImpliesRMPreparedCommittedOrAborted
# ]

twopc_root = StructuredProofNode("Safety", "TCConsistent", children = {
    "RMChooseToAbortAction": [
        tMKnowsPrepareImpliesRMPreparedCommittedOrAborted,
        commitMsgImpliesAllPrepared,
        # rMSentPrepareImpliesNotWorking,
        committedRMImpliesCommitMsg,
    ],
    "RMRcvAbortMsgAction": [
        committedRMImpliesCommitMsg,
        commitMsgImpliesNoAbortMsg
    ],
    "RMRcvCommitMsgAction": [
        commitMsgImpliesNoRMAborted
    ]
})

root = twopc_root
actions = [
    "TMCommit", 
    "TMAbort",
    "TMRcvPreparedAction",
    "RMPrepareAction",
    "RMChooseToAbortAction",
    "RMRcvCommitMsgAction",
    "RMRcvAbortMsgAction"    
]
nodes = []