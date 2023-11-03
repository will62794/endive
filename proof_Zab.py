from proofs import *

#
# Zab proof structure.
#


def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

leaderInLearnerSet = make_node("H_LeaderInLearnerSet")

NodeLOOKINGImpliesELECTIONorDISCOVERY = make_node("H_NodeLOOKINGImpliesELECTIONorDISCOVERY")

ACKEPOCHQuorumImpliesLeaderInSYNCHRONIZATIONorBROADCAST = make_node("H_ACKEPOCHQuorumImpliesLeaderInSYNCHRONIZATIONorBROADCAST")

ACKEPOCHQuorumImpliesAcceptedEpochCorrect = make_node("H_ACKEPOCHQuorumImpliesAcceptedEpochCorrect")

nEWLEADERMsgSentByLeader = make_node("H_NEWLEADERMsgSentByLeader")
nEWLEADERMsgSentByLeader.children = {
    # "TimeoutNoQuorumAction": [
    #     leaderInLearnerSet
    # ],
    # "LeaderProcessACKEPOCHHasBroadcastAction": [   
    #     ACKEPOCHQuorumImpliesAcceptedEpochCorrect,
    #     ACKEPOCHQuorumImpliesLeaderInSYNCHRONIZATIONorBROADCAST
    # ]
}

leaderInDiscoveryImpliesNoNEWLEADERMsgs = make_node("H_LeaderInDiscoveryImpliesNoNEWLEADERMsgs")
leaderInDiscoveryImpliesNoNEWLEADERMsgs.children = {
    "UpdateLeaderAction": [
        nEWLEADERMsgSentByLeader
    ],
    "FollowLeaderMyselfAction": [
        nEWLEADERMsgSentByLeader
    ],
    # "LeaderProcessACKEPOCHHasBroadcastAction": [
    #     ACKEPOCHQuorumImpliesLeaderInSYNCHRONIZATIONorBROADCAST
    # ]
}

NEWLEADERMsgIsPrefixOfSenderLeader = make_node("H_NEWLEADERMsgIsPrefixOfSenderLeader")

aCKMsgImpliesZxidInLog = make_node("H_ACKMsgImpliesZxidInLog")
aCKMsgImpliesZxidInLog.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgIsPrefixOfSenderLeader
    ]
}


NEWLEADERIncomingImpliesLastCommittedBound = make_node("H_NEWLEADERIncomingImpliesLastCommittedBound")

nodeHistoryBoundByLastCommittedIndex = make_node("H_NodeHistoryBoundByLastCommittedIndex")
nodeHistoryBoundByLastCommittedIndex.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERIncomingImpliesLastCommittedBound
    ]
}

COMMITSentByNodeImpliesZxidInLog = make_node("H_COMMITSentByNodeImpliesZxidInLog")

txnWithSameZxidEqualInPROPOSEMessages = make_node("H_TxnWithSameZxidEqualInPROPOSEMessages")

txnWithSameZxidEqualBetweenLocalHistoryAndPROPOSEMessages = make_node("H_TxnWithSameZxidEqualBetweenLocalHistoryAndPROPOSEMessages")

leaderInBroadcastImpliesAllHistoryEntriesInEpoch = make_node("H_LeaderInBroadcastImpliesAllHistoryEntriesInEpoch")

COMMITLDSentByNodeImpliesZxidCommittedInLog = make_node("H_COMMITLDSentByNodeImpliesZxidCommittedInLog")

PROPOSEMsgSentByNodeImpliesZxidInLog = make_node("H_PROPOSEMsgSentByNodeImpliesZxidInLog")

committedEntryExistsInNEWLEADERHistory = make_node("H_CommittedEntryExistsInNEWLEADERHistory")
committedEntryExistsInNEWLEADERHistory.children = {
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "LeaderProcessRequestAction": [
        nodeHistoryBoundByLastCommittedIndex
    ]
}

txnWithSameZxidEqual = make_node("H_TxnWithSameZxidEqual")

committedEntryExistsOnQuorum = make_node("H_CommittedEntryExistsOnQuorum")
committedEntryExistsOnQuorum.children = {
    "LeaderProcessACKAction": [
        aCKMsgImpliesZxidInLog,
        txnWithSameZxidEqual
    ],
    "LeaderProcessRequestAction": [ 
        nodeHistoryBoundByLastCommittedIndex
    ],
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessNEWLEADERAction": [
        committedEntryExistsInNEWLEADERHistory,
        NEWLEADERMsgIsPrefixOfSenderLeader,
        nodeHistoryBoundByLastCommittedIndex
    ]
}

NodeLOOKINGImpliesEmptyInputBuffer = make_node("H_NodeLOOKINGImpliesEmptyInputBuffer")
NodeLOOKINGImpliesEmptyInputBuffer.children = {
    "FollowerProcessNEWLEADERAction": [
        nEWLEADERMsgSentByLeader
    ]
}

committedEntryExistsInACKEPOCHQuorumHistory = make_node("H_CommittedEntryExistsInACKEPOCHQuorumHistory")
committedEntryExistsInACKEPOCHQuorumHistory.children = {
    "LeaderProcessRequestAction": [
        nodeHistoryBoundByLastCommittedIndex
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "FollowerProcessNEWLEADERAction": [
        nodeHistoryBoundByLastCommittedIndex
    ],
    "UpdateLeaderAction":[
        # NodeLOOKINGImpliesELECTIONorDISCOVERY,
        NodeLOOKINGImpliesEmptyInputBuffer
    ],
    "FollowLeaderMyselfAction":[
        # NodeLOOKINGImpliesELECTIONorDISCOVERY,
        NodeLOOKINGImpliesEmptyInputBuffer
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsOnQuorum
    ],
    # "LeaderProcessACKEPOCHHasBroadcastAction": [
    #     committedEntryExistsOnQuorum
    # ]
}   

txnWithSameZxidEqualBetweenLocalHistoryAndMessages = make_node("H_TxnWithSameZxidEqualBetweenLocalHistoryAndMessages")

txnWithSameZxidEqualInMessages = make_node("H_TxnWithSameZxidEqualInMessages")

txnWithSameZxidEqualInPeerHistory = make_node("H_TxnWithSameZxidEqualInPeerHistory")

txnWithSameZxidEqualLocalToPeerHistory = make_node("H_TxnWithSameZxidEqualLocalToPeerHistory")

txnWithSameZxidEqual.children = {
    "FollowerProcessNEWLEADERAction": [
        txnWithSameZxidEqualInMessages,
        txnWithSameZxidEqualBetweenLocalHistoryAndMessages
    ],
    "LeaderProcessRequestAction": [
        leaderInBroadcastImpliesAllHistoryEntriesInEpoch
    ],
    "FollowerProcessPROPOSEAction": [
        # txnWithSameZxidEqualInPROPOSEMessages,
        txnWithSameZxidEqualBetweenLocalHistoryAndPROPOSEMessages
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        txnWithSameZxidEqualInPeerHistory,
        txnWithSameZxidEqualLocalToPeerHistory,
        txnWithSameZxidEqualBetweenLocalHistoryAndMessages
    ]
}


COMMITLDSentByNodeImpliesZxidCommittedInLog.children = {
    # "LeaderProcessACKLDHasBroadcastAction" : [
    #     nodeHistoryBoundByLastCommittedIndex
    # ]
}


safety = make_node("H_PrefixConsistency")

NEWLEADERMsgIsPrefixOfSenderLeader.children = {
    "FollowerProcessNEWLEADERAction": [
        safety,
        nEWLEADERMsgSentByLeader
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        leaderInDiscoveryImpliesNoNEWLEADERMsgs,
        nEWLEADERMsgSentByLeader
    ]
}


committedEntryExistsInLeaderHistory = make_node("H_CommittedEntryExistsInLeaderHistory")
committedEntryExistsInLeaderHistory.children = {
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgIsPrefixOfSenderLeader,
        nEWLEADERMsgSentByLeader
    ],
    "LeaderProcessRequestAction": [
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory
    ],
    "LeaderProcessACKAction": [
        nodeHistoryBoundByLastCommittedIndex
    ]
}


safety.children = {
    "FollowerProcessNEWLEADERAction": [
        # NEWLEADERMsgIsPrefixOfSenderLeader,
        NEWLEADERIncomingImpliesLastCommittedBound,
        nEWLEADERMsgSentByLeader
    ],
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog,
        txnWithSameZxidEqual
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory,        
    ],
    "LeaderProcessACKAction": [
        aCKMsgImpliesZxidInLog
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
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
