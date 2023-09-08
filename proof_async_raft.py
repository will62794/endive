from proofs import *

#
# AbstractStaticRaft proof structure.
#

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")


candidateVotesGrantedInTermAreUnique = StructuredProofNode("CandidateVotesGrantedInTermAreUnique", "H_CandidateVotesGrantedInTermAreUnique")
candidateWithVotesGrantedInTermImplyNoOtherLeader = StructuredProofNode("CandidateWithVotesGrantedInTermImplyNoOtherLeader", "H_CandidateWithVotesGrantedInTermImplyNoOtherLeader")


onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm", "H_OnePrimaryPerTerm", children = {
    "BecomeLeaderAction": [
        candidateVotesGrantedInTermAreUnique,
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ]
})

logTermsMonotonic = StructuredProofNode("LogTermsMonotonic", "H_LogTermsMonotonic")
logTermsMonotonic.children = {
    "ClientRequest": [onePrimaryPerTerm]
}

root = logTermsMonotonic
nodes = [
    # primaryHasEntriesItCreated
]
actions = [
    "RestartAction",
    "RequestVoteAction",
    "BecomeLeaderAction",
    "ClientRequestAction",
    "AdvanceCommitIndexAction",
    "AppendEntriesAction",
    "UpdateTermAction",
    "HandleRequestVoteRequestAction",
    "HandleRequestVoteResponseAction",
    "RejectAppendEntriesRequestAction",
    "AcceptAppendEntriesRequestAction",
    "HandleAppendEntriesResponseAction"
]