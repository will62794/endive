from proofs import *

#
# AbstractStaticRaft proof structure.
#

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")

quorumsSafeAtTerms = StructuredProofNode("QuorumsSafeAtTerms", "H_QuorumsSafeAtTerms")

onePrimaryPerTerm = StructuredProofNode("OnePrimaryPerTerm", "H_OnePrimaryPerTerm", children = {
    "BecomeLeaderAction":[
        quorumsSafeAtTerms
    ]
})
onePrimaryPerTerm.ctigen_typeok = "TypeOKSmallCommitted"


logEntryInTermImpliesSafeAtTerms = StructuredProofNode("LogEntryImpliesSafeAtTerm", "H_LogEntryImpliesSafeAtTerm")
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

PrimaryTermGTELogTerm =  StructuredProofNode("CurrentTermAtLeastAsLargeAsLogTermsForPrimary", "H_PrimaryTermGTELogTerm")
PrimaryTermGTELogTerm.children = {
    "BecomeLeaderAction": [
        logEntryInTermImpliesSafeAtTerms
    ]
}

termsGrowMonotonically = StructuredProofNode("TermsMonotonic", "H_TermsMonotonic")
termsGrowMonotonically.children = {
    "ClientRequestAction": [
        PrimaryTermGTELogTerm
    ]
}
# termsGrowMonotonically.ctigen_typeok = "TypeOKRandomEmptyCommitted"


logMatching = StructuredProofNode("LogMatching", "H_LogMatching", children = {
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
uniformLogEntriesInTerm.ctigen_typeok = "TypeOKSmallCommitted"

entriesCommittedInOwnTerm = StructuredProofNode("EntriesCommittedInOwnTerm", "H_EntriesCommittedInOwnTerm")

primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted = StructuredProofNode("PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted", "H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted")

logsLaterThanCommittedMustHaveCommitted = StructuredProofNode("LaterLogsHaveEarlierCommitted", "H_LaterLogsHaveEarlierCommitted")
# logsLaterThanCommittedMustHaveCommitted.ctigen_typeok = "TypeOKSmallCommitted"
# logsLaterThanCommittedMustHaveCommitted.ctigen_typeok = "TypeOK"

leaderCompleteness = StructuredProofNode("LeaderCompleteness", "H_LeaderCompleteness")

committedEntryExistsOnQuorum = StructuredProofNode("CommittedEntryIsOnQuorum", "H_CommittedEntryIsOnQuorum")
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

coreLogInv = StructuredProofNode("CoreLogInv", "H_UniformLogEntriesInTerm_AND_TermsGrowMonotonically")
coreLogInv.children = {
    "ClientRequestAction": [
        logMatching,
        primaryHasEntriesItCreated,
        PrimaryTermGTELogTerm
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
        termsGrowMonotonically,
        uniformLogEntriesInTerm
    ]
}

leaderCompleteness.children = {
    "BecomeLeaderAction": [
        termsGrowMonotonically,
        uniformLogEntriesInTerm,
        committedEntryExistsOnQuorum,
        logsLaterThanCommittedMustHaveCommitted
    ],
    "CommitEntryAction": [
        termsGrowMonotonically,
        quorumsSafeAtTerms
    ],
}
leaderCompleteness.ctigen_typeok = "TypeOKSmallCommitted2"


asr_children = {
    "CommitEntryAction": [
        # lemmaTRUE
        committedEntryExistsOnQuorum
    ]
}
asr_root = StructuredProofNode("StateMachineSafety", "H_StateMachineSafety", children = asr_children)
asr_nodes = [
    committedEntryExistsOnQuorum,
    logMatching,
    PrimaryTermGTELogTerm
    # primaryHasEntriesItCreated
]
asr_actions = [
    "ClientRequestAction",
    "GetEntriesAction",
    "RollbackEntriesAction",
    "BecomeLeaderAction",
    "CommitEntryAction",
    "UpdateTermsAction"
]