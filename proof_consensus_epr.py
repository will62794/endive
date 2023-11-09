from proofs import *

#
# consensus_epr proof structure.
#

uniqueLeaders = StructuredProofNode("UniqueLeaders","H_UniqueLeaders")
decidedImpliesLeader = StructuredProofNode("DecidedImpliesLeader","H_DecidedImpliesLeader")
leaderHasQuorum = StructuredProofNode("LeaderImpliesVotesInQuorum","H_LeaderHasQuorum")
nodesCantVoteTwice = StructuredProofNode("NodesCantVoteTwice","H_NodesCantVoteTwice")
voteRecordedImpliesNodeVoted = StructuredProofNode("VoteRecordedImpliesNodeVoted","H_VoteRecordedImpliesNodeVoted")
nodesCantSendVotesToDifferentNodes = StructuredProofNode("NodesCantSendVotesToDifferentNodes","H_NodesCantSendVotesToDifferentNodes")
voteMsgImpliesNodeVoted = StructuredProofNode("VoteMsgImpliesNodeVoted","H_VoteMsgImpliesNodeVoted")
voteRecordedImpliesVoteMsg = StructuredProofNode("VoteRecordedImpliesVoteMsg","H_VoteRecordedImpliesVoteMsg")

voteRecordedImpliesNodeVoted.children = {
    "RecvVoteAction": [
        voteMsgImpliesNodeVoted
    ]
}

nodesCantSendVotesToDifferentNodes.children = {
    "SendVoteAction": [
        voteMsgImpliesNodeVoted
    ]
}

nodesCantVoteTwice.children = {
    "RecvVoteAction": [
        # voteRecordedImpliesNodeVoted,
        nodesCantSendVotesToDifferentNodes,
        voteRecordedImpliesVoteMsg
    ]
}

uniqueLeaders.children = {
    "BecomeLeaderAction": [
        leaderHasQuorum,
        nodesCantVoteTwice
    ]
}

children = {
    "DecideAction": [
        uniqueLeaders,
        decidedImpliesLeader
    ]
}

root = StructuredProofNode("NoConflictingValues", "H_NoConflictingValues", children = children)
nodes = [
    uniqueLeaders,
    decidedImpliesLeader,
    leaderHasQuorum,
    nodesCantVoteTwice,
    # voteRecordedImpliesNodeVoted,
    nodesCantSendVotesToDifferentNodes,
    voteMsgImpliesNodeVoted,
    voteRecordedImpliesVoteMsg
]
actions = [
    "SendRequestVoteAction",
    "SendVoteAction",
    "RecvVoteAction",
    "BecomeLeaderAction",
    "DecideAction"
]