from proofs import *

#
# TwoPhase proof structure.
#


tMKnowsPrepareImpliesRMSentPrepare = StructuredProofNode("TMKnowsPrepareImpliesRMSentPrepare", "H_TMKnowsPrepareImpliesRMSentPrepare")

######
######
## lemmaelim
# children = {
#     "TMAbortAction" : ""
#     "TMAbortAction" : StructuredProofNode("InitImpliesNoAbortMsg", "H_InitImpliesNoAbortMsg")
# }
commitMsgImpliesNoAbortMsg = StructuredProofNode("CommitMsgImpliesNoAbortMsg", "H_CommitMsgImpliesNoAbortMsg", children = {
    # lemmaTRUE,
    "TMAbortAction": [
        StructuredProofNode("InitNoCommitMsg", "H_InitNoCommitMsg")
    ],
    "TMCommitAction": [
        StructuredProofNode("InitNoAbortMsg", "H_InitNoAbortMsg")
    ]
})

commitMsgImpliesTMCommitted = StructuredProofNode("CommitMsgImpliesTMCommitted", "H_CommitMsgImpliesTMCommitted")

rMCommittedImpliesNoAbortMsg = StructuredProofNode("RMCommittedImpliesNoAbortMsg", "H_RMCommittedImpliesNoAbortMsg")

rMCommittedImpliesTMCommitted = StructuredProofNode("RMCommittedImpliesTMCommitted", "H_RMCommittedImpliesTMCommitted")
rMCommittedImpliesTMCommitted.children = {
    "RMRcvCommitMsgAction":[
        commitMsgImpliesTMCommitted
    ]
}



abortMsgImpliesTMAborted = StructuredProofNode("AbortMsgImpliesTMAborted", "H_AbortMsgImpliesTMAborted")

rMSentPrepareImpliesNotWorking = StructuredProofNode("RMSentPrepareImpliesNotWorking", "H_RMSentPrepareImpliesNotWorking")

tMKnowsPrepareImpliesRMPreparedCommittedOrAborted = StructuredProofNode(
    "TMKnowsPrepareImpliesRMWorking", 
    "H_TMKnowsPrepareImpliesRMWorking", children = {
        # lemmaTRUE,
        "TMRcvPreparedAction": [rMSentPrepareImpliesNotWorking]
})

rMAbortedAndPreparedImpliesTMAborted = StructuredProofNode("RMAbortedAndPreparedImpliesTMAborted", "H_RMAbortedAndPreparedImpliesTMAborted", children = {
    "RMChooseToAbortAction": [
        tMKnowsPrepareImpliesRMPreparedCommittedOrAborted,
        rMSentPrepareImpliesNotWorking
    ],
    "RMRcvAbortMsgAction": [
        abortMsgImpliesTMAborted,
    ]
})


rMWorkingImpliesNotPrepared = StructuredProofNode("RMWorkingImpliesNotPrepared", "H_RMWorkingImpliesNotPrepared", children = {
    "TMRcvPreparedAction": [
        rMSentPrepareImpliesNotWorking
    ]
})

rMWorkingImpliesNoCommitMsg = StructuredProofNode("RMWorkingImpliesNoCommitMsg", "H_RMWorkingImpliesNoCommitMsg", children = {
    "TMCommitAction": [rMWorkingImpliesNotPrepared]
})

rMAbortedImpliesTMAborted = StructuredProofNode("RMAbortedImpliesTMAborted", "H_RMAbortedImpliesTMAborted")

rMAbortedImpliesNoCommitMsg = StructuredProofNode("RMAbortedImpliesNoCommitMsg", "H_RMAbortedImpliesNoCommitMsg")
rMAbortedImpliesNoCommitMsg.children = {
    "RMChooseToAbortAction": [
        rMWorkingImpliesNoCommitMsg
    ],
    "RMRcvAbortMsgAction":[
        commitMsgImpliesNoAbortMsg
    ],
    "TMCommitAction": [
        rMAbortedAndPreparedImpliesTMAborted
    ]
}

rMCommittedImpliesNoAbortMsg.children = {
    "TMAbortAction":[
        rMCommittedImpliesTMCommitted
    ],
    "RMRcvCommitMsgAction": [
        commitMsgImpliesNoAbortMsg
    ]
}



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
    "TMCommitAction": [tMKnowsPrepareImpliesRMSentPrepare]
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
    "TMCommitAction": [
        allPreparedImpliesAllPreparesSent,
        rMAbortAfterPrepareImpliesTMAborted,
    ]
    
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

commitMsgImpliesAllRMsPreparedOrCommitted = StructuredProofNode("CommitSentImpliesRMsNotWorking", "H_CommitSentImpliesRMsNotWorking")

rMCommittedImpliesOtherRMsPreparedOrCommitted = StructuredProofNode("RMCommittedImpliesNoRMsWorking", "H_RMCommittedImpliesNoRMsWorking")
rMCommittedImpliesOtherRMsPreparedOrCommitted.children = {
    "RMRcvAbortMsgAction": [
        rMCommittedImpliesNoAbortMsg
    ],
    "RMRcvCommitMsgAction": [
        commitMsgImpliesAllRMsPreparedOrCommitted
    ]
}

commitMsgImpliesAllRMsPreparedOrCommitted.children = {
    "RMRcvAbortMsgAction":[commitMsgImpliesNoAbortMsg],
    "TMCommitAction":[
        rMAbortedAndPreparedImpliesTMAborted,
        tMKnowsPrepareImpliesRMPreparedCommittedOrAborted
    ]
}

twopc_root = StructuredProofNode("Safety", "H_TCConsistent", children = {
    "RMChooseToAbortAction": [
        rMCommittedImpliesOtherRMsPreparedOrCommitted
        # tMKnowsPrepareImpliesRMPreparedCommittedOrAborted,
        # commitMsgImpliesAllPrepared,
        # rMSentPrepareImpliesNotWorking,
        # committedRMImpliesCommitMsg,
    ],
    "RMRcvAbortMsgAction": [
        rMCommittedImpliesNoAbortMsg
        # committedRMImpliesCommitMsg,
        # commitMsgImpliesNoAbortMsg
    ],
    "RMRcvCommitMsgAction": [
        # commitMsgImpliesNoRMAborted,
        rMAbortedImpliesNoCommitMsg
    ]
})

root = twopc_root
actions = [
    "TMCommitAction", 
    "TMAbortAction",
    "TMRcvPreparedAction",
    "RMPrepareAction",
    "RMChooseToAbortAction",
    "RMRcvCommitMsgAction",
    "RMRcvAbortMsgAction"    
]
nodes = [rMCommittedImpliesTMCommitted]