from proofs import *

#
# AbstractStaticRaft proof structure.
#

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

quorumsSafeAtTerms = StructuredProofNode("QuorumsSafeAtTerms", "H_QuorumsSafeAtTerms")

onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm_Lemma", "H_OnePrimaryPerTerm", children = {
    # lemmaTRUE,
    "BecomeLeaderAction":[
        quorumsSafeAtTerms
    ]
})
onePrimaryPerTerm.ctigen_typeok = "TypeOKRandomEmptyCommitted"


logEntryInTermImpliesSafeAtTerms = StructuredProofNode("LogEntryInTermImpliesSafeAtTerm", "H_LogEntryInTermImpliesSafeAtTerm")
logEntryInTermImpliesSafeAtTerms.children = {    
    "ClientRequestAction": [
        # quorumsSafeAtTerms
    ]
}

primaryHasEntriesItCreated = StructuredProofNode("PrimaryHasEntriesItCreated_A", "H_PrimaryHasEntriesItCreated")
primaryHasEntriesItCreated.children = {
    # "ClientRequestAction": [
    #     onePrimaryPerTerm,
    # ],
    # "BecomeLeaderAction": [
    #     # quorumsSafeAtTerms,
    #     logEntryInTermImpliesSafeAtTerms
    # ]
}
primaryHasEntriesItCreated.cti_view = "<<state, currentTerm, log>>"
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
        lemmaTRUE,
        # currentTermsAtLeastLargeAsLogTermsForPrimary
    ]
}
# termsGrowMonotonically.ctigen_typeok = "TypeOKRandomEmptyCommitted"


logMatching = StructuredProofNode("LogMatching_Lemma", "LogMatching", children = {
    # "ClientRequestAction":[
    #     lemmaTRUE,
    #     # primaryHasEntriesItCreated
    # ]
})

lemmaTRUEShim.children = {
    "UpdateTermsAction":[primaryHasEntriesItCreated]
}

uniformLogEntriesInTerm = StructuredProofNode("UniformLogEntriesInTerm", "H_UniformLogEntriesInTerm")
uniformLogEntriesInTerm.children = {
    "GetEntriesAction": [
        # lemmaTRUEShim,
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

coreLogInv = StructuredProofNode("CoreLogInv", "H_UniformLogEntriesInTerm_AND_TermsOfEntriesGrowMonotonically")
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

# Alternate proof structure that condense 'UniformLogEntries' and 'TermsGrowMonotonically' into a single,
# central proof node.
alt_children = {
    "BecomeLeaderAction": [
        coreLogInv,
        committedEntryExistsOnQuorum_cycleBreak,
    ],
    "ClientRequestAction": [
        coreLogInv
    ],
    "CommitEntryAction": [
        # termsGrowMonotonically,
        # primaryHasEntriesItCreated,
        logEntryInTermImpliesSafeAtTerms,
        quorumsSafeAtTerms
    ],
    "GetEntriesAction": [
        coreLogInv
    ]
}
# primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted.children = alt_children


logsLaterThanCommittedMustHaveCommitted.children = {
    "ClientRequestAction": [
        # lemmaTRUE,
        leaderCompleteness,
    ],
    "CommitEntryAction": [
        # lemmaTRUE,
        logEntryInTermImpliesSafeAtTerms
    ],
    "GetEntriesAction": [
        lemmaTRUE,
        logMatching,
        termsGrowMonotonically,
    ]
}

leaderCompleteness.children = {
    "BecomeLeaderAction": [
        # lemmaTRUE,
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm,
        # logEntryInTermImpliesSafeAtTerms,
        # # TODO: Will need to deal with cycle recursion issue here properly.
        # committedEntryExistsOnQuorum_cycleBreak,
    ],
    "CommitEntryAction": [
        termsGrowMonotonically,
        quorumsSafeAtTerms
    ],
}


asr_children = {
    "ClientRequestAction": [
        # lemmaTRUE
        committedEntryExistsOnQuorum
    ]
}
asr_root = StructuredProofNode("StateMachineSafety_Lemma", "StateMachineSafety", children = asr_children)
asr_nodes = [
    committedEntryExistsOnQuorum,
    logMatching
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