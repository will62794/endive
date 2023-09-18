from proofs import *

#
# Paxos proof structure.
#


def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")


L1 = make_node("H_L1")
L2 = make_node("H_L2")
L3 = make_node("H_L3")
L4 = make_node("H_NonEmpty1bMsgImpliesAcceptorVotedInPastBallot")
L5 = make_node("H_ValuesSafeAtBallotIn2a")
L6 = make_node("H_UniqueValuesPerBallotIn2aMsgs")
L7 = make_node("H_L7")
L8 = make_node("H_ValueAcceptedAtBallotImpliesCorresponding2a")

L7.children = {
    "Phase2bAction":[
        L1
    ]
}

L4.children = {
    "Phase1bAction":[
        L2
    ]
}

L5.children = {
    "Phase2aAction":[
        L3,
        L4,
        L7
    ]
}

children = {
    "Phase2bAction": [
        L5,
        L6,
        # L7,
        L8
    ]
}
root = StructuredProofNode("Safety", "Inv", children = children)
nodes = [

]
actions = [
    "Phase1aAction",
    "Phase2aAction",
    "Phase1bAction",
    "Phase2bAction"
]