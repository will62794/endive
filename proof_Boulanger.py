from proofs import *

#
# basic_consensus proof structure.
#

def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")


H1 = make_node("H_L1")
H2 = make_node("H_L2")
H3 = make_node("H_L3")
H4 = make_node("H_L4")
H5 = make_node("H_L5")
H6 = make_node("H_L6")
H7 = make_node("H_L7")
H8 = make_node("H_L8")
H9 = make_node("H_L9")

H9.children = {
    "w1Action": [
        H6
    ],
    "w2Action": [
        H2,
        H6,
        H8,
        H7
    ]
}

H7.children = {
    "w1Action": [
        H3
    ]
}

H6.children = {
    "w2Action": [
        H2,
        H8,
        # H9,
        H7
    ]
}
# Comment out stuff below for demo.
children = {
    "w1Action": [
        H9,
        H6
    ],
    "w2Action": [
        H6,
        H8,
        H9
    ]
}

root = make_node("H_MutualExclusion")
root.children = children
nodes = [
    # uniqueLeaders,
    # decidedImpliesLeader,
    # leaderImpliesVotesInQuorum,
    # nodesCantVoteTwice,
    # # voteRecordedImpliesNodeVoted,
    # nodesCantSendVotesToDifferentNodes,
    # voteMsgImpliesNodeVoted,
    # voteRecordedImpliesVoteMsg
]
actions = [
    "SendRequestVoteAction",
    "SendVoteAction",
    "RecvVoteAction",
    "BecomeLeaderAction",
    "DecideAction"
]