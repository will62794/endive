from proofs import *

#
# consensus_epr proof structure.
#

uniqueLeaders = StructuredProofNode("UniqueLeaders","H_UniqueLeaders")
decidedImpliesLeader = StructuredProofNode("DecidedImpliesLeader","H_DecidedImpliesLeader")
leaderImpliesVotesInQuorum = StructuredProofNode("LeaderImpliesVotesInQuorum","H_LeaderImpliesVotesInQuorum")
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
        leaderImpliesVotesInQuorum,
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
    leaderImpliesVotesInQuorum,
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