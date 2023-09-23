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

quorumsSafeAtTerms = make_node("H_QuorumsSafeAtTerms")

logEntryInTermImpliesSafeAtTerms = make_node("H_LogEntryInTermImpliesSafeAtTerm")

candidateInTermVotedForItself = make_node("H_CandidateInTermVotedForItself")

requestVoteRequestFromNodeImpliesSafeAtTerm = make_node("H_RequestVoteRequestFromNodeImpliesSafeAtTerm")

requestVoteResponseToNodeImpliesNodeSafeAtTerm = make_node("H_RequestVoteResponseToNodeImpliesNodeSafeAtTerm")
requestVoteResponseToNodeImpliesNodeSafeAtTerm.children = {
    "HandleRequestVoteRequestAction": [
        requestVoteRequestFromNodeImpliesSafeAtTerm
    ]
}

logEntryInTermImpliesSafeAtTermCandidate = make_node("H_LogEntryInTermImpliesSafeAtTermCandidate")

requestVoteQuorumInTermImpliesNoOtherLogsInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoOtherLogsInTerm")
requestVoteQuorumInTermImpliesNoOtherLeadersInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoOtherLeadersInTerm")

requestVoteQuorumInTermImpliesNoOtherLeadersInTerm.children = {
    "BecomeLeaderAction":[
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm,
        voteGrantedImpliesVoteResponseMsgConsistent
    ],
    "HandleRequestVoteRequestAction":[
        quorumsSafeAtTerms,
        candidateInTermVotedForItself
    ],
    "RequestVoteAction":[
        # quorumsSafeAtTerms,
        requestVoteResponseToNodeImpliesNodeSafeAtTerm
    ]
}

requestVoteQuorumInTermImpliesNoOtherLogsInTerm.children = {
    "ClientRequestAction": [
        requestVoteQuorumInTermImpliesNoOtherLeadersInTerm
    ],
    "HandleRequestVoteRequestAction": [
        logEntryInTermImpliesSafeAtTerms,
        logEntryInTermImpliesSafeAtTermCandidate,
        candidateInTermVotedForItself
    ],
    "RequestVoteAction": [
        logEntryInTermImpliesSafeAtTerms,
        requestVoteResponseToNodeImpliesNodeSafeAtTerm
    ],
}

candidateVotesGrantedInTermAreUnique = StructuredProofNode("CandidateVotesGrantedInTermAreUnique", "H_CandidateVotesGrantedInTermAreUnique")
candidateWithVotesGrantedInTermImplyNoOtherLeader = StructuredProofNode("CandidateWithVotesGrantedInTermImplyNoOtherLeader", "H_CandidateWithVotesGrantedInTermImplyNoOtherLeader")
candidateWithVotesGrantedInTermImplyNoOtherLeader.children = {
    "BecomeLeaderAction": [
        votesCantBeGrantedTwiceToCandidatesInSameTerm
    ],
    "HandleRequestVoteResponseAction":[
        requestVoteQuorumInTermImpliesNoOtherLeadersInTerm,
        requestVoteQuorumInTermImpliesNoOtherLogsInTerm
    ]
}

onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm", "H_OnePrimaryPerTerm", children = {
    "BecomeLeaderAction": [
        # candidateVotesGrantedInTermAreUnique,
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ]
})

candidateWithVotesGrantedInTermImplyVotedForSafeAtTerm = make_node("H_CandidateWithVotesGrantedInTermImplyVotedForSafeAtTerm")

quorumsSafeAtTerms.children = {
    "BecomeLeaderAction": [
        candidateWithVotesGrantedInTermImplyVotersSafeAtTerm,
        candidateInTermVotedForItself
    ]
}

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
        requestVoteQuorumInTermImpliesNoOtherLeadersInTerm,
        requestVoteQuorumInTermImpliesNoOtherLogsInTerm
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
        # requestVoteQuorumInTermImpliesNoOtherLeadersInTerm,
        requestVoteQuorumInTermImpliesNoOtherLogsInTerm
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
    
appendEntriesRequestImpliesSenderSafeAtTerm = make_node("H_AppendEntriesRequestImpliesSenderSafeAtTerm")

appendEntriesResponseInTermImpliesSafeAtTerms = make_node("H_AppendEntriesResponseInTermImpliesSafeAtTerms")

appendEntriesRequestInTermImpliesSafeAtTerms = make_node("H_AppendEntriesRequestInTermImpliesSafeAtTerms")
appendEntriesRequestInTermImpliesSafeAtTerms.children = {
    "AppendEntriesAction": [
        quorumsSafeAtTerms
    ]
}

nodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm = make_node("H_NodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm")
    
nodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm.children = {
    "AppendEntriesAction": [
        quorumsSafeAtTerms
    ],
    "HandleRequestVoteRequestAction": [
        # quorumsSafeAtTerms,
        appendEntriesRequestInTermImpliesSafeAtTerms
    ],
    "RequestVoteAction":[
        # quorumsSafeAtTerms,
        appendEntriesRequestInTermImpliesSafeAtTerms,
        appendEntriesRequestImpliesSenderSafeAtTerm
    ]
}

requestVoteQuorumInTermImpliesNoAppendEntriesInTerm = make_node("H_RequestVoteQuorumInTermImpliesNoAppendEntriesInTerm")
requestVoteQuorumInTermImpliesNoAppendEntriesInTerm.children = {
    "AppendEntriesAction": [
        requestVoteQuorumInTermImpliesNoOtherLeadersInTerm,
        # requestVoteQuorumInTermImpliesNoOtherLogsInTerm
    ],
    "RequestVoteAction": [
        nodesVotedInQuorumInTermImpliesNoAppendEntriesRequestsInTerm,
        appendEntriesRequestInTermImpliesSafeAtTerms
    ],
    "HandleRequestVoteRequestAction": [
        appendEntriesResponseInTermImpliesSafeAtTerms
    ]
}    
    
candidateWithVotesGrantedImpliesNoAppendEntriesInTerm = make_node("H_CandidateWithVotesGrantedImpliesNoAppendEntriesInTerm")
candidateWithVotesGrantedImpliesNoAppendEntriesInTerm.children = {
    "AppendEntriesAction": [
        candidateWithVotesGrantedInTermImplyNoOtherLeader
    ],
    "HandleRequestVoteResponseAction": [
        requestVoteQuorumInTermImpliesNoAppendEntriesInTerm
    ]
}

appendEntriesRequestLogEntriesMustBeInLeaderLog = make_node("H_AppendEntriesRequestLogEntriesMustBeInLeaderLog")
appendEntriesRequestLogEntriesMustBeInLeaderLog.children = {
    "BecomeLeaderAction":[
        candidateWithVotesGrantedImpliesNoAppendEntriesInTerm
    ]
}
    
leaderMatchIndexValidAppendEntries = make_node("H_LeaderMatchIndexValidAppendEntries")
leaderMatchIndexValidAppendEntries.children = {
    "AcceptAppendEntriesRequestAppendAction": [
        appendEntriesRequestLogEntriesMustBeInLeaderLog
    ],
    "BecomeLeaderAction": [
        candidateWithVotesGrantedImpliesNoAppendEntriesInTerm
    ],
    "AcceptAppendEntriesRequestTruncateAction": [
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
        leaderMatchIndexValidAppendEntries,
        logMatching
    ]
}

commitIndexInAppendEntriesImpliesCommittedEntryExists = make_node("H_CommitIndexInAppendEntriesImpliesCommittedEntryExists")

leaderHasEntriesCoveredByCommitIndexes = make_node("H_LeaderHasEntriesCoveredByCommitIndexes")

commitIndexCoversEntryImpliesExistsOnQuorum = make_node("H_CommitIndexCoversEntryImpliesExistsOnQuorum")

noLogDivergence = make_node("H_NoLogDivergence")

noLogDivergenceAppendEntries = make_node("H_NoLogDivergenceAppendEntries")
noLogDivergenceAppendEntries.children = {
    "AppendEntriesAction":[
        # commitIndexCoversEntryImpliesExistsOnQuorum,
        noLogDivergence,
        # leaderHasEntriesCoveredByCommitIndexes,
        # logTermsMonotonic
    ],
    "ClientRequestAction": [
        commitIndexBoundValid
    ]
}

commitIndexCoversEntryImpliesExistsOnQuorum.children = {
    "AcceptAppendEntriesRequestLearnCommitAction": [
        commitIndexInAppendEntriesImpliesCommittedEntryExists,
        logMatching
    ],
    "AdvanceCommitIndexAction": [
        leaderMatchIndexValid
    ],
    "AcceptAppendEntriesRequestTruncateAction": [
        noLogDivergenceAppendEntries
    ]
}


noLogDivergence.children = {
    "AcceptAppendEntriesRequestLearnCommitAction":[
        commitIndexInAppendEntriesImpliesCommittedEntryExists,
        logMatching
    ], 
    "AdvanceCommitIndexAction":[
        leaderMatchIndexValid,
        commitIndexCoversEntryImpliesExistsOnQuorum,
        logMatching
    ],
    "AcceptAppendEntriesRequestTruncateAction": [
        noLogDivergenceAppendEntries
    ]
}
root = noLogDivergence
nodes = [
    primaryHasEntriesItCreated,
    requestVoteQuorumInTermImpliesNoOtherLeadersInTerm
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