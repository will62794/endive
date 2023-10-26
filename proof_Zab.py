from proofs import *

#
# Zab proof structure.
#


def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")


safety = make_node("H_PrefixConsistency")
safety.children = {}

root = safety
nodes = [

]
actions = [
    "UpdateLeaderAction",
    "FollowLeaderAction",
    "TimeoutAction",
    "RestartAction",
    "ConnectAndFollowerSendCEPOCHAction",
    "LeaderProcessCEPOCHAction",
    "FollowerProcessNEWEPOCHAction",
    "LeaderProcessACKEPOCHAction",
    "FollowerProcessNEWLEADERAction",
    "LeaderProcessACKLDAction",
    "FollowerProcessCOMMITLDAction",
    "LeaderProcessRequestAction",
    "LeaderBroadcastPROPOSEAction",
    "FollowerProcessPROPOSEAction",
    "LeaderProcessACKAction",
    "FollowerProcessCOMMITAction",
    "FilterNonexistentMessageAction"
]
