from proofs import *

#
# consensus_epr proof structure.
#

uniqueLeaders = StructuredProofNode("UniqueLeaders","H_UniqueLeaders")
decidedImpliesLeader = StructuredProofNode("DecidedImpliesLeader","H_DecidedImpliesLeader")
leaderImpliesVotesInQuorum = StructuredProofNode("LeaderImpliesVotesInQuorum","H_LeaderImpliesVotesInQuorum")
nodesCantVoteTwice = StructuredProofNode("NodesCantVoteTwice","H_NodesCantVoteTwice")
voteRecordedImpliesNodeVoted = StructuredProofNode("VoteRecordedImpliesNodeVoted","H_VoteRecordedImpliesNodeVoted")
nodesCantSentVotesToDifferentNodes = StructuredProofNode("NodesCantSentVotesToDifferentNodes","H_NodesCantSentVotesToDifferentNodes")
voteMsgImpliesNodeVoted = StructuredProofNode("VoteMsgImpliesNodeVoted","H_VoteMsgImpliesNodeVoted")
voteRecordedImpliesVoteMsg = StructuredProofNode("VoteRecordedImpliesVoteMsg","H_VoteRecordedImpliesVoteMsg")

voteRecordedImpliesNodeVoted.children = {
    "RecvVoteAction": [
        voteMsgImpliesNodeVoted
    ]
}

nodesCantSentVotesToDifferentNodes.children = {
    "SendVoteAction": [
        voteMsgImpliesNodeVoted
    ]
}

nodesCantVoteTwice.children = {
    "RecvVoteAction": [
        voteRecordedImpliesNodeVoted,
        nodesCantSentVotesToDifferentNodes,
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

root = StructuredProofNode("Safety", "SafetyInv", children = children)
nodes = [
]
actions = [
    "SendRequestVoteAction",
    "SendVoteAction",
    "RecvVoteAction",
    "BecomeLeaderAction",
    "DecideAction"
]