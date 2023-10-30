from proofs import *

#
# Zab proof structure.
#


def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

aCKMsgImpliesZxidInLog = make_node("H_ACKMsgImpliesZxidInLog")

committedEntryExistsInACKEPOCHQuorumHistory = make_node("H_CommittedEntryExistsInACKEPOCHQuorumHistory")

txnWithSameZxidEqual = make_node("H_TxnWithSameZxidEqual")

nodeHistoryBoundByLastCommittedIndex = make_node("H_NodeHistoryBoundByLastCommittedIndex")

COMMITLDSentByNodeImpliesZxidCommittedInLog = make_node("H_COMMITLDSentByNodeImpliesZxidCommittedInLog")
COMMITLDSentByNodeImpliesZxidCommittedInLog.children = {
    "LeaderProcessACKLDHasntBroadcastAction" : [
        nodeHistoryBoundByLastCommittedIndex
    ]
}

COMMITSentByNodeImpliesZxidInLog = make_node("H_COMMITSentByNodeImpliesZxidInLog")

NEWLEADERMsgIsPrefixOfSenderLeader = make_node("H_NEWLEADERMsgIsPrefixOfSenderLeader")
safety = make_node("H_PrefixConsistency")

NEWLEADERMsgIsPrefixOfSenderLeader.children = {
    "FollowerProcessNEWLEADERAction": [
        safety
    ]
}

safety.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgIsPrefixOfSenderLeader
    ],
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog,
        txnWithSameZxidEqual
    ],
    "LeaderProcessACKEPOCHNoNewLeaderHasQuorumAction": [
        committedEntryExistsInACKEPOCHQuorumHistory
    ],
    "LeaderProcessACKAction": [
        aCKMsgImpliesZxidInLog
    ]
}

root = safety
nodes = [

]
actions = [
    # "UpdateLeaderAction",
    # "FollowLeaderMyselfAction",
    # "FollowLeaderOtherAction",
    # "TimeoutAction",
    # "RestartAction",
    # "ConnectAndFollowerSendCEPOCHAction",
    # "LeaderProcessCEPOCHAction",
    # "FollowerProcessNEWEPOCHAction",
    # "LeaderProcessACKEPOCHAction",
    # "FollowerProcessNEWLEADERAction",
    # "FollowerProcessNEWLEADERNewIterationAction",
    # "LeaderProcessACKLDAction",
    # "FollowerProcessCOMMITLDAction",
    # "LeaderProcessRequestAction",
    # "LeaderBroadcastPROPOSEAction",
    # "FollowerProcessPROPOSEAction",
    # "LeaderProcessACKAction",
    # "FollowerProcessCOMMITAction",
    # "FilterNonexistentMessageAction"
]
