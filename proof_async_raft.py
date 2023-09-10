from proofs import *

#
# AbstractStaticRaft proof structure.
#

def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

appendEntriesNeverSentToSelf = make_node("H_AppendEntriesNeverSentToSelf")
requestVotesNeverSentToSelf = make_node("H_RequestVotesNeverSentToSelf")


candidateWithVotesGrantedInTermImplyVotersSafeAtTerm = make_node("H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm")

votesCantBeGrantedTwiceToCandidatesInSameTerm = make_node("H_VotesCantBeGrantedTwiceToCandidatesInSameTerm")
votesCantBeGrantedTwiceToCandidatesInSameTerm.children = {
    "RequestVoteAction": [
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm
    ]
}

candidateVotesGrantedInTermAreUnique = StructuredProofNode("CandidateVotesGrantedInTermAreUnique", "H_CandidateVotesGrantedInTermAreUnique")
candidateWithVotesGrantedInTermImplyNoOtherLeader = StructuredProofNode("CandidateWithVotesGrantedInTermImplyNoOtherLeader", "H_CandidateWithVotesGrantedInTermImplyNoOtherLeader")
candidateWithVotesGrantedInTermImplyNoOtherLeader.children = {
    "BecomeLeaderAction": [
        votesCantBeGrantedTwiceToCandidatesInSameTerm
    ]
}

onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm", "H_OnePrimaryPerTerm", children = {
    "BecomeLeaderAction": [
        # candidateVotesGrantedInTermAreUnique,
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ]
})


quorumsSafeAtTerms = make_node("H_QuorumsSafeAtTerms")
quorumsSafeAtTerms.children = {
    "BecomeLeaderAction": [
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm
    ]
}

logEntryInTermImpliesSafeAtTerms = make_node("H_LogEntryInTermImpliesSafeAtTerm")
logEntryInTermImpliesSafeAtTermAppendEntries = make_node("H_LogEntryInTermImpliesSafeAtTermAppendEntries")

logEntryInTermImpliesSafeAtTermAppendEntries.children = {
    "AppendEntriesAction":[
        logEntryInTermImpliesSafeAtTerms
    ]
}

logEntryInTermImpliesSafeAtTerms.children = {
    "ClientRequestAction": [
        quorumsSafeAtTerms
    ],
    "AcceptAppendEntriesRequestAppendAction": [
        logEntryInTermImpliesSafeAtTermAppendEntries
    ]
}

successfulRequestVoteQuorumInTermImpliesNoLogsInTerm = make_node("H_SuccessfulRequestVoteQuorumInTermImpliesNoLogsInTerm")

candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm = make_node("H_CandidateWithVotesGrantedInTermImplyNoOtherLogsInTerm")
candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm.children = {
    "ClientRequestAction":[
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ],
    "RequestVoteAction":[
        logEntryInTermImpliesSafeAtTerms
    ],
    # "HandleRequestVoteResponseAction": [
    #     # successfulRequestVoteQuorumInTermImpliesNoLogsInTerm,
    #     # requestVotesNeverSentToSelf
    # ]
}

currentTermsAtLeastLargeAsLogTermsForPrimary =  StructuredProofNode("CurrentTermAtLeastAsLargeAsLogTermsForPrimary", "H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary")
currentTermsAtLeastLargeAsLogTermsForPrimary.children = {
    "BecomeLeaderAction": [
        logEntryInTermImpliesSafeAtTerms,
        candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
    ]
}

logTermsMonotonic = StructuredProofNode("LogTermsMonotonic", "H_LogTermsMonotonic")
logTermsMonotonic.children = {
    "ClientRequestAction": [
        # onePrimaryPerTerm,
        currentTermsAtLeastLargeAsLogTermsForPrimary
    ]
}

requestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm")
requestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm")
requestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm.children = {
    "AppendEntriesAction": [
        requestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm
    ]
}

candidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm = make_node("H_CandidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm")
candidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm.children = {
    "AppendEntriesAction": [
        candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
    ],
    "HandleRequestVoteResponseAction": [
        requestVoteQuorumInTermImpliesNoAppendEntryLogsInTerm,
    ]
}

primaryHasEntriesItCreated = make_node("H_PrimaryHasEntriesItCreated")
primaryHasEntriesItCreatedAppendEntries = make_node("H_PrimaryHasEntriesItCreatedAppendEntries")

primaryHasEntriesItCreatedAppendEntries.children = {
    "AppendEntriesAction": [primaryHasEntriesItCreated],
    "BecomeLeaderAction": [candidateWithVotesGrantedInTermImplyNoAppendEntryLogsInTerm]
}

primaryHasEntriesItCreated.children = {
    "ClientRequestAction":[
        onePrimaryPerTerm
    ],
    "BecomeLeaderAction": [
        candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
    ],
    "AcceptAppendEntriesRequestAppendAction": [
        primaryHasEntriesItCreatedAppendEntries
    ]
}


divergentEntriesInAppendEntriesMsgs = make_node("H_DivergentEntriesInAppendEntriesMsgs")
divergentEntriesInAppendEntriesMsgs.children = {
    "AppendEntriesAction":[
        primaryHasEntriesItCreated,
        # candidateWithVotesGrantedInTermImplyNoOtherLeader,
        candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
    ], 
    "RequestVoteAction":[
        logEntryInTermImpliesSafeAtTermAppendEntries
    ]
}

logMatching = StructuredProofNode("LogMatching", "H_LogMatching")

logMatchingInAppendEntriesMsgs = make_node("H_LogMatchingInAppendEntriesMsgs")
logMatchingInAppendEntriesMsgs.children = {
    "ClientRequestAction": [
        divergentEntriesInAppendEntriesMsgs
    ],
    "AppendEntriesAction":[
        logMatching
    ]
}

logMatching.children = {
    "ClientRequestAction":[
        primaryHasEntriesItCreated
    ],
    "AcceptAppendEntriesRequestAppendAction":[
        logMatchingInAppendEntriesMsgs
    ]
}

commitIndexBoundValid = make_node("H_CommitIndexBoundValid")
    
leaderMatchIndexValid = make_node("H_LeaderMatchIndexValid")

commitIndexCoversEntryImpliesExistsOnQuorum = make_node("H_CommitIndexCoversEntryImpliesExistsOnQuorum")
commitIndexCoversEntryImpliesExistsOnQuorum.children = {
    "AdvanceCommitIndexAction": [
        leaderMatchIndexValid
    ]
}

noLogDivergence = make_node("H_NoLogDivergence")
noLogDivergence.children = {
    # "AcceptAppendEntriesRequestAppendAction":[
    #     appendEntriesNeverSentToSelf
    # ], 
    "AdvanceCommitIndexAction":[
        leaderMatchIndexValid,
        commitIndexCoversEntryImpliesExistsOnQuorum,
        logMatching
    ]
}
root = noLogDivergence
nodes = [
    primaryHasEntriesItCreated
]
actions = [
    "RequestVoteAction",
    "BecomeLeaderAction",
    "ClientRequestAction",
    "AdvanceCommitIndexAction",
    "AppendEntriesAction",
    "UpdateTermAction",
    "HandleRequestVoteRequestAction",
    "HandleRequestVoteResponseAction",
    "RejectAppendEntriesRequestAction",
    "AcceptAppendEntriesRequestAppendAction",
    "AcceptAppendEntriesRequestTruncateAction",
    "HandleAppendEntriesResponseAction"
]