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

LeaderInBroadcastImpliesNoNEWEPOCHInFlight = make_node("H_LeaderInBroadcastImpliesNoNEWEPOCHInFlight")

PROPOSEMsgInFlightImpliesNodesInBROADCAST = make_node("H_PROPOSEMsgInFlightImpliesNodesInBROADCAST")

NEWLEADERMsgHistAndStateInv = make_node("H_NEWLEADERMsgHistAndStateInv")

PROPOSEMsgSentByNodeImpliesZxidInLog = make_node("H_PROPOSEMsgSentByNodeImpliesZxidInLog")

aCKMsgImpliesZxidInLog = make_node("H_ACKMsgImpliesZxidInLog")
aCKMsgImpliesZxidInLog.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv
    ],
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST,
        PROPOSEMsgSentByNodeImpliesZxidInLog
    ]
}

LeaderInDISCOVERYImpliesNoCOMMITs = make_node("H_LeaderInDISCOVERYImpliesNoCOMMITs")

ACKLDImpliesNoNewACKEPOCHFromMe = make_node("H_ACKLDImpliesNoNewACKEPOCHFromMe")

NEWLEADERIncomingImpliesNoIncomingCOMMIT = make_node("H_NEWLEADERIncomingImpliesNoIncomingCOMMIT")
NEWLEADERIncomingImpliesNoIncomingCOMMIT.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        LeaderInDISCOVERYImpliesNoCOMMITs,

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

COMMITLDSentByNodeImpliesZxidCommittedInLog = make_node("H_COMMITLDSentByNodeImpliesZxidCommittedInLog")

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
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
}

ACKMsgInFlightImpliesNodesInBROADCAST = make_node("H_ACKMsgInFlightImpliesNodesInBROADCAST")

COMMITSentByNodeImpliesZxidInLog = make_node("H_COMMITSentByNodeImpliesZxidInLog")
COMMITSentByNodeImpliesZxidInLog.children = {
    "LeaderProcessACKAction": [
        ACKMsgInFlightImpliesNodesInBROADCAST
    ]
}

txnZxidsUniqueHistoriesAndMessagesInPROPOSEMessages = make_node("H_txnZxidsUniqueHistoriesAndMessagesInPROPOSEMessages")

txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndPROPOSEMessages = make_node("H_txnZxidsUniqueHistoriesAndMessagesBetweenLocalHistoryAndPROPOSEMessages")

NodeLOOKINGImpliesNoIncomingACKEPOCH = make_node("H_NodeLOOKINGImpliesNoIncomingACKEPOCH")

NodeCantSendCEPOCHToDifferentLeaders = make_node("H_NodeCantSendCEPOCHToDifferentLeaders")

UniqueEstablishedLeaderImpliesSafeAtEpoch = make_node("H_UniqueEstablishedLeaderImpliesSafeAtEpoch")

uniqueLeadership = make_node("H_UniqueLeadership")

UniqueEstablishedLeaderImpliesNEWEPOCHsFromThem = make_node("H_UniqueEstablishedLeaderImpliesNEWEPOCHsFromThem")
UniqueEstablishedLeaderImpliesNEWEPOCHsFromThem.children = {
    "LeaderProcessCEPOCHAction": [
        NodeCantSendCEPOCHToDifferentLeaders,
        UniqueEstablishedLeaderImpliesSafeAtEpoch,
        uniqueLeadership
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
}

UniqueEstablishedLeaderImpliesSafeAtEpoch.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
    "UpdateLeaderAction": [
        NodeLOOKINGImpliesNoIncomingACKEPOCH
    ],
    "FollowLeaderMyselfAction": [
        NodeLOOKINGImpliesNoIncomingACKEPOCH
    ],
    "FollowerProcessNEWEPOCHAction": [  
        UniqueEstablishedLeaderImpliesNEWEPOCHsFromThem
    ]
}

uniqueLeadership.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        UniqueEstablishedLeaderImpliesSafeAtEpoch
    ],
}   

NEWLEADERMsgImpliesNoLogEntriesInEpoch = make_node("H_NEWLEADERMsgImpliesNoLogEntriesInEpoch")
NEWLEADERMsgImpliesNoLogEntriesInEpoch.children = {
    "LeaderProcessRequestAction": [
        uniqueLeadership
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        NEWLEADERMsgHistAndStateInv
    ]
}

UniqueEstablishedLeader = make_node("H_UniqueEstablishedLeader")

leaderInBroadcastImpliesHasAllEntriesInEpoch = make_node("H_LeaderInBroadcastImpliesHasAllEntriesInEpoch")
leaderInBroadcastImpliesHasAllEntriesInEpoch.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgSentByNodeImpliesZxidInLog
    ],
    "LeaderProcessRequestAction": [
        UniqueEstablishedLeader
    ],
    "FollowerProcessNEWLEADERAction": [ 
        # Can remove maybe?
        NEWLEADERMsgHistAndStateInv
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ]
    # "LeaderProcessACKLDHasntBroadcastAction": [
    #     # NEWLEADERMsgImpliesNoLogEntriesInEpoch
    # ]
}

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

ACKEPOCHImpliesSenderSafeAtEpoch = make_node("H_ACKEPOCHImpliesSenderSafeAtEpoch")

ACKLDMsgSentByFollowerImpliesEmptyBuffer = make_node("H_ACKLDMsgSentByFollowerImpliesEmptyBuffer")

EstablishedLeaderImpliesSafeAtCurrentEpoch = make_node("H_EstablishedLeaderImpliesSafeAtCurrentEpoch")
EstablishedLeaderImpliesSafeAtCurrentEpoch.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        # ACKEPOCHImpliesSenderSafeAtEpoch
    ]
}

LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight = make_node("H_LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight")
LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight.children = {
    # "LeaderProcessACKEPOCHHasntBroadcastAction": [
        # uniqueLeadership
    # ],
    # "FollowerProcessNEWEPOCHAction": [
    #     EstablishedLeaderImpliesSafeAtCurrentEpoch
    # ],
    "LeaderProcessACKLDHasntBroadcastAction": [
        # ACKLDMsgSentByFollowerImpliesEmptyBuffer
        ACKLDImpliesNoNewACKEPOCHFromMe
    ]
}

NodeLOOKINGImpliesNoIncomingNEWEPOCH = make_node("H_NodeLOOKINGImpliesNoIncomingNEWEPOCH")

# LeaderImpliesLearnersFollowing = make_node("H_LeaderImpliesLearnersFollowing")

FollowerCantBeLearnerToDifferentLeaders = make_node("H_FollowerCantBeLearnerToDifferentLeaders")
FollowerCantBeLearnerToDifferentLeaders.children = {
    "FollowLeaderMyselfAction": [
        NodeLOOKINGImpliesNoIncomingNEWEPOCH
    ],
    "UpdateLeaderAction":[
        NodeLOOKINGImpliesNoIncomingNEWEPOCH
    ]
}

ACKEPOCHMsgImpliesSenderFollowing = make_node("H_ACKEPOCHMsgImpliesSenderFollowing")

LeaderInBROADCASTImpliesLearnerInBROADCAST = make_node("H_LeaderInBROADCASTImpliesLearnerInBROADCAST")
LeaderInBROADCASTImpliesLearnerInBROADCAST.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender,
        # ACKEPOCHMsgImpliesSenderFollowing
    ],
    "TimeoutNoQuorumAction": [
        FollowerCantBeLearnerToDifferentLeaders
    ],
}

PROPOSEMsgInFlightImpliesNodesInBROADCAST.children = {
    "LeaderBroadcastPROPOSEAction": [
        # LeaderInBROADCASTImpliesAckLDQuorum,
        LeaderInBROADCASTImpliesLearnerInBROADCAST
    ],
    # "FollowerProcessNEWEPOCHAction": [
        # LeaderInBroadcastImpliesNoNEWEPOCHInFlight
    # ]
}

ACKMsgInFlightImpliesNodesInBROADCAST.children = {
    "FollowerProcessPROPOSEAction": [
        PROPOSEMsgInFlightImpliesNodesInBROADCAST
    ]
}


NEWLEADERUniquePerEpoch = make_node("H_NEWLEADERUniquePerEpoch")

# NEWLEADERHistoryExistsOnQuorum = make_node("H_NEWLEADERHistoryExistsOnQuorum")
# NEWLEADERHistoryExistsOnQuorum.children = {
#     "LeaderProcessACKEPOCHHasntBroadcastAction": [
#         ACKEPOCHHistoryContainedInFOLLOWINGSender
#     ]
# }

ACKLDMsgImpliesZxidInLog = make_node("H_ACKLDMsgImpliesZxidInLog")
ACKLDMsgImpliesZxidInLog.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv
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
    # "FollowerProcessCOMMITAction": [
        # NEWLEADERIncomingImpliesNoIncomingCOMMIT
    # ]
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
        COMMITSentByNodeImpliesZxidInLog,
        txnZxidsUniqueHistoriesAndMessages
    ],
    "FollowerProcessCOMMITLDAction": [
        COMMITLDSentByNodeImpliesZxidCommittedInLog
    ],
    "FollowerProcessPROPOSEAction": [
        nodeHistoryBoundByLastCommittedIndex,
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
    "FollowerProcessPROPOSEAction": [
        NodeLOOKINGImpliesEmptyInputBuffer
    ],
    "TimeoutNoQuorumAction": [

    ]
}

LeaderImpliesNotInELECTION = make_node("H_LeaderImpliesNotInELECTION")

NodeLOOKINGImpliesNoIncomingCEPOCH = make_node("H_NodeLOOKINGImpliesNoIncomingCEPOCH")

NodeLOOKINGImpliesNoIncomingNEWEPOCH.children = {
    "LeaderProcessCEPOCHAction": [
        NodeLOOKINGImpliesNoIncomingCEPOCH
    ],
    "TimeoutNoQuorumAction": [
        LeaderImpliesNotInELECTION,
        LeaderInBROADCASTImpliesLearnerInBROADCAST,
        FollowerCantBeLearnerToDifferentLeaders
    ]
}

NodeLOOKINGImpliesNoIncomingACKEPOCH.children = {
    "FollowerProcessNEWEPOCHAction": [
        NodeLOOKINGImpliesNoIncomingNEWEPOCH
    ]
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
        NodeLOOKINGImpliesNoIncomingACKEPOCH
    ],
    "FollowLeaderMyselfAction":[
        # NodeLOOKINGImpliesELECTIONorDISCOVERY,
        NodeLOOKINGImpliesNoIncomingACKEPOCH
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
    "LeaderProcessACKLDHasntBroadcastAction": [
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
    "FollowerProcessNEWEPOCHAction": [
        committedEntryExistsOnQuorum,
        ACKEPOCHHistoryContainedInFOLLOWINGSender
    ],
    "FollowerProcessPROPOSEAction": [
        nodeHistoryBoundByLastCommittedIndex
    ]
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
        # LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight,
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
        # LeaderinBROADCASTImpliesNoNEWLEADERorACKEInFlight,
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

ACKEPOCHFromNodeImpliesCEPOCHRecvd = make_node("H_ACKEPOCHFromNodeImpliesCEPOCHRecvd")
ACKEPOCHFromNodeImpliesCEPOCHRecvd.children = {
    "FollowerProcessNEWEPOCHAction": [
        NEWEPOCHFromNodeImpliesLEADING
    ]
}

LeaderCEPOCHRecvsUnique = make_node("H_LeaderCEPOCHRecvsUnique")

CEPOCHRecvsAreLearners = make_node("H_CEPOCHRecvsAreLearners")
CEPOCHRecvsAreLearners.children = {
    "LeaderProcessCEPOCHAction": [
        LeaderCEPOCHRecvsUnique
    ]
    # "TimeoutNoQuorum":[

    # ]
}


NodeLOOKINGImpliesNotInOtherCEPOCHRecv = make_node("H_NodeLOOKINGImpliesNotInOtherCEPOCHRecv")
NodeLOOKINGImpliesNotInOtherCEPOCHRecv.children = {
    "LeaderProcessCEPOCHAction": [
        LeaderCEPOCHRecvsUnique
    ],
    "TimeoutNoQuorumAction": [
        CEPOCHRecvsAreLearners
    ],
}

LeaderCEPOCHsUnique = make_node("H_LeaderCEPOCHsUnique")
LeaderCEPOCHsUnique.children = {
    "FollowLeaderMyselfAction": [
        # NodeLOOKINGImpliesNoIncomingCEPOCH,
        # NodeLOOKINGImpliesNotInOtherCEPOCHRecv
    ],
    "UpdateLeaderAction": [
        # NodeLOOKINGImpliesNotInOtherCEPOCHRecv
    ],    
}

LeaderCEPOCHMsgsUnique = make_node("H_LeaderCEPOCHMsgsUnique")
LeaderCEPOCHRecvsUnique.children  = {
    "LeaderProcessCEPOCHAction": [
        LeaderCEPOCHMsgsUnique
    ]
}

TwoLeadersCantHaveSameCEPOCH = make_node("H_TwoLeadersCantHaveSameCEPOCH")
TwoLeadersCantHaveSameCEPOCH.children = {
    "FollowLeaderMyselfAction": [
        # NodeLOOKINGImpliesNoIncomingCEPOCH,
        NodeLOOKINGImpliesNotInOtherCEPOCHRecv
    ],
    "UpdateLeaderAction": [
        NodeLOOKINGImpliesNotInOtherCEPOCHRecv
    ],
    "LeaderProcessCEPOCHAction": [
        # LeaderCEPOCHsUnique,
        # LeaderCEPOCHMsgsUnique,
        LeaderCEPOCHRecvsUnique
    ]
}

ACKEPOCHMsgsOnlyMustMatchRecv = make_node("H_ACKEPOCHMsgsOnlyMustMatchRecv")
ACKEPOCHMsgsOnlyMustMatchRecv.children = {
    "FollowerProcessNEWEPOCHAction": [
        NEWEPOCHFromNodeImpliesLEADING,
        TwoLeadersCantHaveSameCEPOCH
    ],
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHFromNodeImpliesCEPOCHRecvd,
        TwoLeadersCantHaveSameCEPOCH
    ]
}

UniqueEstablishedLeader.children = {
    "LeaderProcessACKEPOCHHasntBroadcastAction": [
        ACKEPOCHMsgsOnlyMustMatchRecv
    ],
}

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
        # uniqueLeadership,
        UniqueEstablishedLeader
    ]
}


safety.children = {
    "FollowerProcessNEWLEADERAction": [
        NEWLEADERMsgHistAndStateInv,
        committedEntryExistsInNEWLEADERHistory
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
