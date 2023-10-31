from proofs import *

#
# Zab proof structure.
#


def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

leaderInDiscoveryImpliesNoNEWLEADERMsgs = make_node("H_LeaderInDiscoveryImpliesNoNEWLEADERMsgs")

NEWLEADERMsgIsPrefixOfSenderLeader = make_node("H_NEWLEADERMsgIsPrefixOfSenderLeader")

aCKMsgImpliesZxidInLog = make_node("H_ACKMsgImpliesZxidInLog")
aCKMsgImpliesZxidInLog.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgIsPrefixOfSenderLeader
    ]
}

leaderInBroadcastImpliesAllHistoryEntriesInEpoch = make_node("H_LeaderInBroadcastImpliesAllHistoryEntriesInEpoch")

committedEntryExistsInACKEPOCHQuorumHistory = make_node("H_CommittedEntryExistsInACKEPOCHQuorumHistory")

txnWithSameZxidEqualBetweenLocalHistoryAndMessages = make_node("H_TxnWithSameZxidEqualBetweenLocalHistoryAndMessages")

txnWithSameZxidEqualInMessages = make_node("H_TxnWithSameZxidEqualInMessages")

txnWithSameZxidEqual = make_node("H_TxnWithSameZxidEqual")
txnWithSameZxidEqual.children = {
    "FollowerProcessNEWLEADERAction": [
        txnWithSameZxidEqualInMessages,
        txnWithSameZxidEqualBetweenLocalHistoryAndMessages
    ],
    "LeaderProcessRequestAction": [
        leaderInBroadcastImpliesAllHistoryEntriesInEpoch
    ]
}

nodeHistoryBoundByLastCommittedIndex = make_node("H_NodeHistoryBoundByLastCommittedIndex")

COMMITLDSentByNodeImpliesZxidCommittedInLog = make_node("H_COMMITLDSentByNodeImpliesZxidCommittedInLog")
COMMITLDSentByNodeImpliesZxidCommittedInLog.children = {
    "LeaderProcessACKLDHasntBroadcastAction" : [
        nodeHistoryBoundByLastCommittedIndex
    ]
}

COMMITSentByNodeImpliesZxidInLog = make_node("H_COMMITSentByNodeImpliesZxidInLog")

safety = make_node("H_PrefixConsistency")

NEWLEADERMsgIsPrefixOfSenderLeader.children = {
    "FollowerProcessNEWLEADERAction": [
        safety
    ],
    "LeaderProcessACKEPOCHNoNewLeaderHasQuorumAction": [
        leaderInDiscoveryImpliesNoNEWLEADERMsgs
    ]
}

NEWLEADERIncomingImpliesLastCommittedBound = make_node("H_NEWLEADERIncomingImpliesLastCommittedBound")

committedEntryExistsInLeaderHistory = make_node("H_CommittedEntryExistsInLeaderHistory")

safety.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgIsPrefixOfSenderLeader,
        NEWLEADERIncomingImpliesLastCommittedBound
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
    ],
    "LeaderProcessACKLDHasBroadcastHasQuorumAction": [
        committedEntryExistsInLeaderHistory
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
