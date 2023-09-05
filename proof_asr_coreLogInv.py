from proofs import *

#
# AbstractStaticRaft proof structure.
#

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

quorumsSafeAtTerms = StructuredProofNode("QuorumsSafeAtTerms", "H_QuorumsSafeAtTerms")

onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm_Lemma", "H_OnePrimaryPerTerm", children = {
    "BecomeLeaderAction":[
        quorumsSafeAtTerms
    ]
})
onePrimaryPerTerm.ctigen_typeok = "TypeOKRandomEmptyCommitted"


logEntryInTermImpliesSafeAtTerms = StructuredProofNode("LogEntryInTermImpliesSafeAtTerm", "H_LogEntryInTermImpliesSafeAtTerm")
logEntryInTermImpliesSafeAtTerms.children = {    
    "ClientRequestAction": [
        quorumsSafeAtTerms
    ]
}

primaryHasEntriesItCreated = StructuredProofNode("PrimaryHasEntriesItCreated", "H_PrimaryHasEntriesItCreated")
primaryHasEntriesItCreated.children = {
    "ClientRequestAction": [
        onePrimaryPerTerm,
    ],
    "BecomeLeaderAction": [
        # quorumsSafeAtTerms,
        logEntryInTermImpliesSafeAtTerms
    ]
}
# primaryHasEntriesItCreated.cti_view = "<<state, currentTerm, log>>"
primaryHasEntriesItCreated.cti_project_vars = ["state", "currentTerm", "log"]

currentTermsAtLeastLargeAsLogTermsForPrimary =  StructuredProofNode("CurrentTermAtLeastAsLargeAsLogTermsForPrimary", "H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary")
currentTermsAtLeastLargeAsLogTermsForPrimary.children = {
    "BecomeLeaderAction": [
        logEntryInTermImpliesSafeAtTerms
    ]
}

termsGrowMonotonically = StructuredProofNode("TermsOfEntriesGrowMonotonically", "H_TermsOfEntriesGrowMonotonically")
termsGrowMonotonically.children = {
    "ClientRequestAction": [
        currentTermsAtLeastLargeAsLogTermsForPrimary
    ]
}
# termsGrowMonotonically.ctigen_typeok = "TypeOKRandomEmptyCommitted"


logMatching = StructuredProofNode("LogMatching_Lemma", "LogMatching", children = {
    "ClientRequestAction":[
        primaryHasEntriesItCreated
    ]
})

lemmaTRUEShim.children = {
    "UpdateTermsAction":[primaryHasEntriesItCreated]
}

uniformLogEntriesInTerm = StructuredProofNode("UniformLogEntriesInTerm", "H_UniformLogEntriesInTerm")
uniformLogEntriesInTerm.children = {
    "GetEntriesAction": [
        logMatching
    ],
    "ClientRequestAction": [
        primaryHasEntriesItCreated
    ]
}
uniformLogEntriesInTerm.ctigen_typeok = "TypeOKRandomEmptyCommitted"

entriesCommittedInOwnTerm = StructuredProofNode("EntriesCommittedInOwnTerm", "H_EntriesCommittedInOwnTerm")

primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted = StructuredProofNode("PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted", "H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted")

logsLaterThanCommittedMustHaveCommitted = StructuredProofNode("LogsLaterThanCommittedMustHaveCommitted", "H_LogsLaterThanCommittedMustHaveCommitted")
# logsLaterThanCommittedMustHaveCommitted.ctigen_typeok = "TypeOKSmallCommitted"
logsLaterThanCommittedMustHaveCommitted.ctigen_typeok = "TypeOK"

leaderCompleteness = StructuredProofNode("LeaderCompletenessLemma", "LeaderCompleteness")

committedEntryExistsOnQuorum = StructuredProofNode("CommittedEntryExistsOnQuorum", "H_CommittedEntryExistsOnQuorum")
committedEntryExistsOnQuorum.children = {
    "RollbackEntriesAction":[
        # lemmaTRUE,
        logsLaterThanCommittedMustHaveCommitted

        # primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted
        # StructuredProofNode("LogsLaterThanCommittedMustHaveCommitted", "H_LogsLaterThanCommittedMustHaveCommitted", children = [lemmaTRUE]),
        # StructuredProofNode("LeaderCompletenessLemma", "LeaderCompleteness", children = [lemmaTRUE])
        # primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted,
        # logsLaterThanCommittedMustHaveCommitted,
        # leaderCompleteness
    ]
}
committedEntryExistsOnQuorum.ctigen_typeok = "TypeOKSmallCommitted"

coreLogInv = StructuredProofNode("CoreLogInv", "H_CoreLogInv")
coreLogInv.children = {
    "ClientRequestAction": [
        logMatching,
        primaryHasEntriesItCreated,
        currentTermsAtLeastLargeAsLogTermsForPrimary
    ]
}

committedEntryExistsOnQuorum_cycleBreak = StructuredProofNode("CommittedEntryExistsOnQuorum_cycleBreak", "H_CommittedEntryExistsOnQuorum_cyclebreak")

# TODO: May need to figure out how to deal with cyclic dependency here.
primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted.children = {
    "BecomeLeaderAction": [
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm,
        # committedEntryExistsOnQuorum_cycleBreak
        # logEntryInTermImpliesSafeAtTerms,
    ],
    "ClientRequestAction": [
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm,
    ],
    "CommitEntryAction": [
        # logEntryInTermImpliesSafeAtTerms,
        # quorumsSafeAtTerms
        # termsGrowMonotonically,
        # primaryHasEntriesItCreated,
    ],
    "GetEntriesAction": [
        lemmaTRUE
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm
    ]
}

logsLaterThanCommittedMustHaveCommitted.children = {
    "ClientRequestAction": [
        leaderCompleteness,
    ],
    "CommitEntryAction": [
        logEntryInTermImpliesSafeAtTerms
    ],
    "GetEntriesAction": [
        coreLogInv
    ]
}

leaderCompleteness.children = {
    "BecomeLeaderAction": [
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm,
        coreLogInv,
        committedEntryExistsOnQuorum,
        logsLaterThanCommittedMustHaveCommitted
    ],
    "CommitEntryAction": [
        # termsGrowMonotonically,
        coreLogInv,
        quorumsSafeAtTerms
    ],
}


asr_children = {
    "CommitEntryAction": [
        # lemmaTRUE
        committedEntryExistsOnQuorum
    ]
}
asr_root = StructuredProofNode("StateMachineSafety_Lemma", "StateMachineSafety", children = asr_children)
asr_nodes = [
    committedEntryExistsOnQuorum,
    logMatching,
    currentTermsAtLeastLargeAsLogTermsForPrimary,
    coreLogInv
    # primaryHasEntriesItCreated
]
asr_actions = [
    "ClientRequestAction",
    "GetEntriesAction",
    "RollbackEntriesAction",
    "BecomeLeaderAction",
    "CommitEntryAction",
    "UpdateTermsActions"
]
