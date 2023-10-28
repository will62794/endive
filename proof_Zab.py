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
