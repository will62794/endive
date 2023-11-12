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
        nEWLEADERMsgSentByLeader,
    ],
    "FollowLeaderMyselfAction": [
        nEWLEADERMsgSentByLeader
    ],
    # "LeaderProcessACKEPOCHHasBroadcastAction": [
    #     ACKEPOCHQuorumImpliesLeaderInSYNCHRONIZATIONorBROADCAST
    # ]
}

PROPOSEMsgInFlightImpliesNodesInBROADCAST = make_node("H_PROPOSEMsgInFlightImpliesNodesInBROADCAST")

NEWLEADERMsgHistAndStateInv = make_node("H_NEWLEADERMsgHistAndStateInv")

aCKMsgImpliesZxidInLog = make_node("H_ACKMsgImpliesZxidInLog")
aCKMsgImpliesZxidInLog.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv
    ],
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST
    ]
}


NEWLEADERIncomingImpliesLastCommittedBound = make_node("H_NEWLEADERIncomingImpliesLastCommittedBound")

committedEntryExistsInACKEPOCHQuorumHistory = make_node("H_CommittedEntryExistsInACKEPOCHQuorumHistory")

nodeHistoryBoundByLastCommittedIndex = make_node("H_NodeHistoryBoundByLastCommittedIndex")
nodeHistoryBoundByLastCommittedIndex.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERIncomingImpliesLastCommittedBound
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory
    ],
}


NEWEPOCHFromNodeImpliesLEADING = make_node("H_NEWEPOCHFromNodeImpliesLEADING")

ACKEPOCHHistoryContainedInFOLLOWINGSender = make_node("H_ACKEPOCHHistoryContainedInFOLLOWINGSender")
ACKEPOCHHistoryContainedInFOLLOWINGSender.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST
    ],
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv
    ],
    "FollowerProcessNEWEPOCHAction": [
        NEWEPOCHFromNodeImpliesLEADING
    ]   
}

ACKMsgInFlightImpliesNodesInBROADCAST = make_node("H_ACKMsgInFlightImpliesNodesInBROADCAST")

PROPOSEMsgSentByNodeImpliesZxidInLog = make_node("H_PROPOSEMsgSentByNodeImpliesZxidInLog")

COMMITSentByNodeImpliesZxidInLog = make_node("H_COMMITSentByNodeImpliesZxidInLog")
COMMITSentByNodeImpliesZxidInLog.children = {
    "LeaderProcessACKAction": [
        ACKMsgInFlightImpliesNodesInBROADCAST
    ]
}

txnZxidsUniqueHistoriesAndMessagesInPROPOSEMessages = make_node("H_txnZxidsUniqueHistoriesAndMessagesInPROPOSEMessages")

txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndPROPOSEMessages = make_node("H_txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndPROPOSEMessages")

uniqueLeadership = make_node("H_UniqueLeadership")

NEWLEADERMsgImpliesNoLogEntriesInEpoch = make_node("H_NEWLEADERMsgImpliesNoLogEntriesInEpoch")
NEWLEADERMsgImpliesNoLogEntriesInEpoch.children = {
    "LeaderProcessRequestAction": [
        uniqueLeadership
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        NEWLEADERMsgHistAndStateInv
    ]
}

leaderInBroadcastImpliesHasAllEntriesInEpoch = make_node("H_LeaderInBroadcastImpliesHasAllEntriesInEpoch")
leaderInBroadcastImpliesHasAllEntriesInEpoch.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgSentByNodeImpliesZxidInLog
    ],
    "LeaderProcessRequestAction": [
        uniqueLeadership
    ],
    "FollowerProcessNEWLEADERAction": [ 
        NEWLEADERMsgHistAndStateInv
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ]
    # "LeaderProcessACKLDHasntBroadcastAction": [
    #     # NEWLEADERMsgImpliesNoLogEntriesInEpoch
    # ]
}

COMMITLDSentByNodeImpliesZxidCommittedInLog = make_node("H_COMMITLDSentByNodeImpliesZxidCommittedInLog")
COMMITLDSentByNodeImpliesZxidCommittedInLog.children = {
    "FollowerProcessNEWLEADERAction": [ 
        NEWLEADERMsgHistAndStateInv
    ]
}

ServerInEntryAckSidImpliesHasEntry = make_node("H_ServerInEntryAckSidImpliesHasEntry")


AckLDRecvsAreConnected = make_node("H_AckLDRecvsAreConnected")

LeaderInBROADCASTImpliesAckLDQuorum = make_node("H_LeaderInBROADCASTImpliesAckLDQuorum")
LeaderInBROADCASTImpliesAckLDQuorum.children = {
    "LeaderProcessACKLDHasntBroadcastAction": [
        AckLDRecvsAreConnected
    ]
}

ACKLDMsgSentByFollowerImpliesEmptyBuffer = make_node("H_ACKLDMsgSentByFollowerImpliesEmptyBuffer")

LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight = make_node("H_LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight")
LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        uniqueLeadership
    ],
    # "LeaderProcessACKLDHasntBroadcastAction": [
    #     ACKLDMsgSentByFollowerImpliesEmptyBuffer
    # ]
}

LeaderInBROADCASTImpliesLearnerInBROADCAST = make_node("H_LeaderInBROADCASTImpliesLearnerInBROADCAST")
LeaderInBROADCASTImpliesLearnerInBROADCAST.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        # ACKLDMsgSentByFollowerImpliesEmptyBuffer
    ]
}

PROPOSEMsgInFlightImpliesNodesInBROADCAST.children = {
    "LeaderBroadcastPROPOSEAction": [
        # LeaderInBROADCASTImpliesAckLDQuorum,
        LeaderInBROADCASTImpliesLearnerInBROADCAST
    ]
}

ACKMsgInFlightImpliesNodesInBROADCAST.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST
    ]
}


NEWLEADERUniquePerEpoch = make_node("H_NEWLEADERUniquePerEpoch")

NEWLEADERHistoryExistsOnQuorum = make_node("H_NEWLEADERHistoryExistsOnQuorum")
NEWLEADERHistoryExistsOnQuorum.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ]
}

ACKLDMsgImpliesZxidInLog = make_node("H_ACKLDMsgImpliesZxidInLog")
ACKLDMsgImpliesZxidInLog.children = {
    "FollowerProcessNEWLEADERAction": [
        # NEWLEADERHistoryExistsOnQuorum
    ]
}

committedEntryExistsInNEWLEADERHistory = make_node("H_CommittedEntryExistsInNEWLEADERHistory")
committedEntryExistsInNEWLEADERHistory.children = {
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "LeaderProcessRequestAction": [
        nodeHistoryBoundByLastCommittedIndex
    ],
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv,
    ],
    "LeaderProcessACKAction": [
        aCKMsgImpliesZxidInLog,
        ACKMsgInFlightImpliesNodesInBROADCAST
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory,
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        ACKLDMsgImpliesZxidInLog
    ],
    "FollowerProcessPROPOSEAction": [
        nodeHistoryBoundByLastCommittedIndex
    ]
}

NEWLEADERIncomingImpliesLastCommittedBound.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInNEWLEADERHistory,
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKAction": [
        NEWLEADERMsgHistAndStateInv
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ]
}

txnZxidsUniqueHistoriesAndMessages = make_node("H_TxnZxidsUniqueHistoriesAndMessages")


committedEntryExistsOnQuorum = make_node("H_CommittedEntryExistsOnQuorum")
committedEntryExistsOnQuorum.children = {
    "LeaderProcessACKAction": [
        aCKMsgImpliesZxidInLog,
        txnZxidsUniqueHistoriesAndMessages
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
        NEWLEADERMsgHistAndStateInv,
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory,
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        ACKLDMsgImpliesZxidInLog
    ]
}

FollowersHaveNoMessagesSentToSelf = make_node("H_FollowersHaveNoMessagesSentToSelf")

NodeLOOKINGImpliesEmptyInputBuffer = make_node("H_NodeLOOKINGImpliesEmptyInputBuffer")
NodeLOOKINGImpliesEmptyInputBuffer.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv
    ],
    "FollowerProcessNEWEPOCHAction": [
        FollowersHaveNoMessagesSentToSelf
    ],
    # "LeaderProcessACKLDHasntBroadcastAction": [
    #     NodeLOOKINGImpliesELECTIONorDISCOVERY
    # ]
}


committedEntryExistsInACKEPOCHQuorumHistory.children = {
    "LeaderProcessRequestAction": [
        nodeHistoryBoundByLastCommittedIndex
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "FollowerProcessNEWLEADERAction": [
        nodeHistoryBoundByLastCommittedIndex,
        committedEntryExistsInNEWLEADERHistory
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
        # committedEntryExistsOnQuorum,
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "LeaderProcessACKAction": [
        ACKMsgInFlightImpliesNodesInBROADCAST
    ],
    "LeaderProcessACKEPOCHHasBroadcastAction": [
        committedEntryExistsOnQuorum,
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
    "FollowerProcessNEWEPOCHAction": [
        committedEntryExistsOnQuorum,
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
}   

# txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndMessages = make_node("H_txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndMessages")
# txnZxidUniqueBetweenLocalHistoriesAndAllMessages = make_node("H_TxnZxidUniqueBetweenLocalHistoriesAndAllMessages")
# txnZxidsUniqueHistoriesAndMessagesBetweenAllMessages = make_node("H_txnZxidsUniqueHistoriesAndMessagesBetweenAllMessages")

# txnZxidsUniqueHistoriesAndMessagesInPeerHistory = make_node("H_txnZxidsUniqueHistoriesAndMessagesInPeerHistory")
# txnZxidsUniqueHistoriesAndMessagesLocalToPeerHistory = make_node("H_txnZxidsUniqueHistoriesAndMessagesLocalToPeerHistory")

TxnWithSameZxidEqualPeerHistory = make_node("H_TxnWithSameZxidEqualPeerHistory")
TxnWithSameZxidEqualPeerHistory.children = {
    "FollowLeaderMyselfAction": [
        txnZxidsUniqueHistoriesAndMessages
    ],
    "UpdateLeaderAction": [
        txnZxidsUniqueHistoriesAndMessages
    ],
    "LeaderProcessRequestAction": [
        LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight,
        txnZxidsUniqueHistoriesAndMessages,
        leaderInBroadcastImpliesHasAllEntriesInEpoch
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        # committedEntryExistsInACKEPOCHQuorumHistory
        txnZxidsUniqueHistoriesAndMessages
    ]
}

txnZxidsUniqueHistoriesAndMessages.children = {
    # "FollowerProcessNEWLEADERAction": [
    #     # txnZxidsUniqueHistoriesAndMessagesBetweenAllMessages,
    #     # txnZxidUniqueBetweenLocalHistoriesAndAllMessages
    # ],
    "LeaderProcessRequestAction": [
        leaderInBroadcastImpliesHasAllEntriesInEpoch,
        LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight,
        PROPOSEMsgSentByNodeImpliesZxidInLog
    ],
    # "FollowerProcessPROPOSEAction": [
    #     # txnZxidsUniqueHistoriesAndMessagesInPROPOSEMessages,
    #     # txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndPROPOSEMessages,
    #     # txnZxidUniqueBetweenLocalHistoriesAndAllMessages
    # ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        # txnZxidsUniqueHistoriesAndMessagesInPeerHistory,
        # txnZxidsUniqueHistoriesAndMessagesLocalToPeerHistory,
        TxnWithSameZxidEqualPeerHistory,
        # txnZxidUniqueBetweenLocalHistoriesAndAllMessages
    ]
}

# txnZxidUniqueBetweenLocalHistoriesAndAllMessages.children = {
#     "FollowerProcessNEWEPOCHAction": [
#         txnZxidsUniqueHistoriesAndMessages
#     ],
#     "LeaderBroadcastPROPOSEAction": [
#         txnZxidsUniqueHistoriesAndMessages
#     ],
#     "LeaderProcessACKEPOCHHasntBroadcastAction": [

#     ],
#     "LeaderProcessRequestAction": [

#     ]
# }


safety = make_node("H_PrefixConsistency")

NEWLEADERMsgHistAndStateInv.children = {
    # "FollowerProcessNEWLEADERAction": [
    #     # safety,
    #     # nEWLEADERMsgSentByLeader
    # ],
    # "LeaderProcessACKEPOCHHasntBroadcastAction": [
    #     # leaderInDiscoveryImpliesNoNEWLEADERMsgs,
    #     # nEWLEADERMsgSentByLeader
    # ]
}

UniqueEstablishedLeader = make_node("H_UniqueEstablishedLeader")

committedEntryExistsInLeaderHistory = make_node("H_CommittedEntryExistsInLeaderHistory")
committedEntryExistsInLeaderHistory.children = {
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog
    ],
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv,
        # nEWLEADERMsgSentByLeader
    ],
    "LeaderProcessRequestAction": [
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory,
        nodeHistoryBoundByLastCommittedIndex
    ],
    "LeaderProcessACKAction": [
        nodeHistoryBoundByLastCommittedIndex,
        aCKMsgImpliesZxidInLog
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgSentByNodeImpliesZxidInLog
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        UniqueEstablishedLeader
    ]
}


safety.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv,
        # NEWLEADERIncomingImpliesLastCommittedBound,
        # nEWLEADERMsgSentByLeader
    ],
    "FollowerProcessCOMMITAction": [
        COMMITSentByNodeImpliesZxidInLog,
        txnZxidsUniqueHistoriesAndMessages
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog,
        txnZxidsUniqueHistoriesAndMessages
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        committedEntryExistsInACKEPOCHQuorumHistory,        
    ],
    "LeaderProcessACKAction": [
        aCKMsgImpliesZxidInLog,
        txnZxidsUniqueHistoriesAndMessages
    ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        committedEntryExistsInLeaderHistory,
        txnZxidsUniqueHistoriesAndMessages
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
