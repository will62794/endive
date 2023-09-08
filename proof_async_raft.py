from proofs import *

#
# AbstractStaticRaft proof structure.
#

def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

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

candidateWithVotesGrantedInTermImplyVotersSafeAtTerm = make_node("H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm")

quorumsSafeAtTerms = make_node("H_QuorumsSafeAtTerms")
quorumsSafeAtTerms.children = {
    "BecomeLeaderAction": [
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm
    ]
}

logEntryInTermImpliesSafeAtTerms = StructuredProofNode("LogEntryInTermImpliesSafeAtTerm", "H_LogEntryInTermImpliesSafeAtTerm", children = {
    "ClientRequestAction": [
        quorumsSafeAtTerms
    ]
})

currentTermsAtLeastLargeAsLogTermsForPrimary =  StructuredProofNode("CurrentTermAtLeastAsLargeAsLogTermsForPrimary", "H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary")
currentTermsAtLeastLargeAsLogTermsForPrimary.children = {
    "BecomeLeaderAction": [
        logEntryInTermImpliesSafeAtTerms
    ]
}

logTermsMonotonic = StructuredProofNode("LogTermsMonotonic", "H_LogTermsMonotonic")
logTermsMonotonic.children = {
    "ClientRequestAction": [
        # onePrimaryPerTerm,
        currentTermsAtLeastLargeAsLogTermsForPrimary
    ]
}

primaryHasEntriesItCreated = make_node("H_PrimaryHasEntriesItCreated")
primaryHasEntriesItCreated.children = {
    "ClientRequestAction":[
        onePrimaryPerTerm
    ]
}

lemmaTRUEShim.children = {
    "BecomeLeaderAction":[
        logTermsMonotonic,
        primaryHasEntriesItCreated
    ]
}
root = lemmaTRUEShim
nodes = [
    primaryHasEntriesItCreated
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