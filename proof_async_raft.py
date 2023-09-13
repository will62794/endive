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


requestVoteResponseTermsMatchSource = make_node("H_RequestVoteResponseTermsMatchSource")

candidateWithVotesGrantedInTermImplyVotersSafeAtTerm = make_node("H_CandidateWithVotesGrantedInTermImplyVotersSafeAtTerm")
candidateWithVotesGrantedInTermImplyVotersSafeAtTerm.children = {
    "HandleRequestVoteResponseAction": [
        requestVoteResponseTermsMatchSource
    ]
}

voteInGrantedImpliesVotedFor = make_node("H_VoteInGrantedImpliesVotedFor")
voteInGrantedImpliesVotedFor.children = {
    "UpdateTerm":[
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm
    ],
    "HandleRequestVoteResponseAction":[
        requestVoteResponseTermsMatchSource
    ]
}

voteGrantedImpliesVoteResponseMsgConsistent = make_node("H_VoteGrantedImpliesVoteResponseMsgConsistent")
voteGrantedImpliesVoteResponseMsgConsistent.children = {
    "RequestVoteAction": [
        requestVoteResponseTermsMatchSource
    ],
    "HandleRequestVoteRequestAction": [
        voteInGrantedImpliesVotedFor
    ]
}

votesCantBeGrantedTwiceToCandidatesInSameTerm = make_node("H_VotesCantBeGrantedTwiceToCandidatesInSameTerm")
votesCantBeGrantedTwiceToCandidatesInSameTerm.children = {
    "RequestVoteAction": [
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm
    ],
    "HandleRequestVoteResponseAction": [
        voteGrantedImpliesVoteResponseMsgConsistent
    ]
}

requestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm")

candidateVotesGrantedInTermAreUnique = StructuredProofNode("CandidateVotesGrantedInTermAreUnique", "H_CandidateVotesGrantedInTermAreUnique")
candidateWithVotesGrantedInTermImplyNoOtherLeader = StructuredProofNode("CandidateWithVotesGrantedInTermImplyNoOtherLeader", "H_CandidateWithVotesGrantedInTermImplyNoOtherLeader")
candidateWithVotesGrantedInTermImplyNoOtherLeader.children = {
    "BecomeLeaderAction": [
        votesCantBeGrantedTwiceToCandidatesInSameTerm
    ],
    "HandleRequestVoteResponseAction":[
        requestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm
    ]
}

onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm", "H_OnePrimaryPerTerm", children = {
    "BecomeLeaderAction": [
        # candidateVotesGrantedInTermAreUnique,
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ]
})

candidateWithVotesGrantedInTermImplyVotedForSafeAtTerm = make_node("H_CandidateWithVotesGrantedInTermImplyVotedForSafeAtTerm")

quorumsSafeAtTerms = make_node("H_QuorumsSafeAtTerms")
quorumsSafeAtTerms.children = {
    "BecomeLeaderAction": [
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm,
        # candidateWithVotesGrantedInTermImplyVotedForSafeAtTerm
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
    "HandleRequestVoteResponseAction": [
        requestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm
    ]
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

divergentEntriesInAppendEntriesMsgsForRequestVoteQuorum = make_node("H_DivergentEntriesInAppendEntriesMsgsForRequestVoteQuorum")


divergentEntriesInAppendEntriesMsgs = make_node("H_DivergentEntriesInAppendEntriesMsgs")
divergentEntriesInAppendEntriesMsgs.children = {
    "AppendEntriesAction":[
        primaryHasEntriesItCreated,
        # candidateWithVotesGrantedInTermImplyNoOtherLeader,
        candidateWithVotesGrantedInTermImplyNoOtherLogsInTerm
    ], 
    "RequestVoteAction":[
        logEntryInTermImpliesSafeAtTermAppendEntries
    ],
    "HandleRequestVoteResponseAction":[
        divergentEntriesInAppendEntriesMsgsForRequestVoteQuorum
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
    

appendEntriesRequestInTermImpliesSafeAtTerms = make_node("H_AppendEntriesRequestInTermImpliesSafeAtTerms")

nodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm = make_node("H_NodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm")
    
requestVoteQuorumInTermImpliesNoAppendEntriesRequestsInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoAppendEntriesRequestsInTerm")
requestVoteQuorumInTermImpliesNoAppendEntriesRequestsInTerm.children = {
    "AppendEntriesAction": [
        requestVoteQuorumInTermImpliesNoOtherLogsOrLeadersInTerm
    ],
    "RequestVoteAction": [
        nodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm,
        appendEntriesRequestInTermImpliesSafeAtTerms
    ]
}    
    
candidateWithVotesGrantedImpliesNoAppendEntriesRequestsInTerm = make_node("H_CandidateWithVotesGrantedImpliesNoAppendEntriesRequestsInTerm")
candidateWithVotesGrantedImpliesNoAppendEntriesRequestsInTerm.children = {
    "AppendEntriesAction": [
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ],
    "HandleRequestVoteResponseAction": [
        requestVoteQuorumInTermImpliesNoAppendEntriesRequestsInTerm
    ]
}

appendEntriesRequestLogEntriesMustBeInLeaderLog = make_node("H_AppendEntriesRequestLogEntriesMustBeInLeaderLog")
appendEntriesRequestLogEntriesMustBeInLeaderLog.children = {
    "BecomeLeaderAction":[
        candidateWithVotesGrantedImpliesNoAppendEntriesRequestsInTerm
    ]
}
    
leaderMatchIndexValidAppendEntries = make_node("H_LeaderMatchIndexValidAppendEntries")
leaderMatchIndexValidAppendEntries.children = {
    "AcceptAppendEntriesRequestAppendAction": [
        appendEntriesRequestLogEntriesMustBeInLeaderLog
    ]
}
    

leaderMatchIndexBound = make_node("H_LeaderMatchIndexBound")
leaderMatchIndexBound.children = {
    "HandleAppendEntriesResponseAction": [
        leaderMatchIndexValidAppendEntries
    ]
}

leaderMatchIndexValid = make_node("H_LeaderMatchIndexValid")
leaderMatchIndexValid.children = {
    "ClientRequestAction": [
        leaderMatchIndexBound
    ],
    "HandleAppendEntriesResponseAction": [
        leaderMatchIndexValidAppendEntries
    ],
    "AcceptAppendEntriesRequestTruncateAction": [

    ]
}

commitIndexInAppendEntriesImpliesCommittedEntryExists = make_node("H_CommitIndexInAppendEntriesImpliesCommittedEntryExists")


commitIndexCoversEntryImpliesExistsOnQuorum = make_node("H_CommitIndexCoversEntryImpliesExistsOnQuorum")
commitIndexCoversEntryImpliesExistsOnQuorum.children = {
    "AcceptAppendEntriesRequestLearnCommitAction": [
        commitIndexInAppendEntriesImpliesCommittedEntryExists,
        logMatching
    ],
    "AdvanceCommitIndexAction": [
        leaderMatchIndexValid
    ]
}


noLogDivergence = make_node("H_NoLogDivergence")
noLogDivergence.children = {
    "AcceptAppendEntriesRequestLearnCommitAction":[
        commitIndexInAppendEntriesImpliesCommittedEntryExists,
        logMatching
    ], 
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
    "UpdateTerm",
    "HandleRequestVoteRequestAction",
    "HandleRequestVoteResponseAction",
    "RejectAppendEntriesRequestAction",
    "AcceptAppendEntriesRequestAppendAction",
    "AcceptAppendEntriesRequestTruncateAction",
    "AcceptAppendEntriesRequestLearnCommitAction",
    "HandleAppendEntriesResponseAction"
]