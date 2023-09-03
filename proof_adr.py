from proofs import *


#
# AbstractDynamicRaft proof structure.
#

configsNonEmpty_adr = StructuredProofNode("ConfigsNonempty", "H_ConfigsNonempty")

quorumsSafeAtTerms_adr = StructuredProofNode("QuorumsSafeAtTerms", "H_QuorumsSafeAtTerms")
quorumsSafeAtTerms_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"

primaryConfigTermEqualToCurrentTerm_adr = StructuredProofNode("PrimaryConfigTermEqualToCurrentTerm", "H_PrimaryConfigTermEqualToCurrentTerm")
primaryConfigTermEqualToCurrentTerm_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"

activeConfigsOverlap_adr = StructuredProofNode("ActiveConfigsOverlap", "H_ActiveConfigsOverlap")
activeConfigsSafeAtTerms_adr = StructuredProofNode("ActiveConfigsSafeAtTerms", "H_ActiveConfigsSafeAtTerms")

onePrimaryPerTerm_adr = StructuredProofNode("OnePrimaryPerTerm_Lemma", "H_OnePrimaryPerTerm")

primaryInTermContainsNewestConfigOfTerm_adr = StructuredProofNode("PrimaryInTermContainsNewestConfigOfTerm", "H_PrimaryInTermContainsNewestConfigOfTerm")
primaryInTermContainsNewestConfigOfTerm_adr.children = {
    "BecomeLeaderAction": [
        activeConfigsSafeAtTerms_adr,
        # TODO: will need to deal with cycle issue here before re-including this lemma.
        onePrimaryPerTerm_adr
    ],
    "ReconfigAction": [
        onePrimaryPerTerm_adr,
        primaryConfigTermEqualToCurrentTerm_adr
    ]
}
primaryInTermContainsNewestConfigOfTerm_adr.ctigen_typeok = "TypeOKEmptyCommittedEmptyLogs"


configVersionAndTermUnique_adr = StructuredProofNode("ConfigVersionAndTermUnique", "H_ConfigVersionAndTermUnique")
# configVersionAndTermUnique_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"
configVersionAndTermUnique_adr.ctigen_typeok = "TypeOK"
configVersionAndTermUnique_adr.children = {
    "BecomeLeaderAction":[
        primaryConfigTermEqualToCurrentTerm_adr,
        activeConfigsSafeAtTerms_adr,
    ],
    "ReconfigAction": [
        primaryInTermContainsNewestConfigOfTerm_adr,
        primaryConfigTermEqualToCurrentTerm_adr
    ]
}

activeConfigsOverlap_adr.children = {
    "ReconfigAction": [
        onePrimaryPerTerm_adr,
        activeConfigsSafeAtTerms_adr
    ],
    "BecomeLeaderAction": [
        activeConfigsSafeAtTerms_adr
    ]
}

activeConfigsSafeAtTerms_adr.children = {
    "BecomeLeaderAction": [activeConfigsOverlap_adr],
    "ReconfigAction": [
        activeConfigsOverlap_adr,
    ]
}



onePrimaryPerTerm_adr.children = {
    # lemmaTRUE,
    "BecomeLeaderAction": [
        # quorumsSafeAtTerms_adr,
        primaryConfigTermEqualToCurrentTerm_adr,
        configVersionAndTermUnique_adr,
        # primaryInTermContainsNewestConfigOfTerm_adr,
        activeConfigsOverlap_adr,
        activeConfigsSafeAtTerms_adr
    ]
}
onePrimaryPerTerm_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"

logEntryInTermImpliesConfigInTerm = StructuredProofNode("LogEntryInTermImpliesConfigInTerm", "H_LogEntryInTermImpliesConfigInTerm")

primaryHasEntriesItCreated_adr = StructuredProofNode("PrimaryHasEntriesItCreated_A", "H_PrimaryHasEntriesItCreated")
primaryHasEntriesItCreated_adr.children = {
    "ClientRequestAction": [
        onePrimaryPerTerm_adr,
    ],
    "BecomeLeaderAction": [
        logEntryInTermImpliesConfigInTerm,
        activeConfigsSafeAtTerms_adr
    ]
}
primaryHasEntriesItCreated_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"



logMatching_adr = StructuredProofNode("LogMatching_Lemma", "LogMatching", children = {
    "ClientRequestAction":[primaryHasEntriesItCreated_adr]
})
logMatching_adr.ctigen_typeok = "TypeOKEmptyCommitted"

currentTermsAtLeastLargeAsLogTermsForPrimary_adr =  StructuredProofNode("CurrentTermAtLeastAsLargeAsLogTermsForPrimary", "H_CurrentTermAtLeastAsLargeAsLogTermsForPrimary")
currentTermsAtLeastLargeAsLogTermsForPrimary_adr.children = {
    "BecomeLeaderAction": [
        activeConfigsSafeAtTerms_adr,
        logEntryInTermImpliesConfigInTerm
    ]
}


termsGrowMonotonically_adr = StructuredProofNode("TermsOfEntriesGrowMonotonically", "H_TermsOfEntriesGrowMonotonically")
termsGrowMonotonically_adr.children = {
    "ClientRequestAction": [
        currentTermsAtLeastLargeAsLogTermsForPrimary_adr
    ]
}

uniformLogEntriesInTerm_adr = StructuredProofNode("UniformLogEntriesInTerm", "H_UniformLogEntriesInTerm")
uniformLogEntriesInTerm_adr.children = {
    "GetEntriesAction": [
        # lemmaTRUEShim,
        logMatching_adr
    ],
    "ClientRequestAction": [
        primaryHasEntriesItCreated_adr
    ]
}
uniformLogEntriesInTerm_adr.ctigen_typeok = "TypeOKEmptyCommitted"

activeConfigsOverlapWithCommittedEntry_adr = StructuredProofNode("ActiveConfigsOverlapWithCommittedEntry", "H_ActiveConfigsOverlapWithCommittedEntry")
newerConfigsDisablePrimaryCommitsInOlderTerms_adr = StructuredProofNode("NewerConfigsDisablePrimaryCommitsInOlderTerms", "H_NewerConfigsDisablePrimaryCommitsInOlderTerms")

primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted_adr = StructuredProofNode("PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted", "H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted")
primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted_adr.children = {
    "BecomeLeaderAction": [
        termsGrowMonotonically_adr,
        # uniformLogEntriesInTerm,
        # logEntryInTermImpliesSafeAtTerms,
        # committedEntryExistsOnQuorum_cycleBreak
    ],
    "ClientRequestAction": [
        termsGrowMonotonically_adr,
        uniformLogEntriesInTerm_adr,
    ],
    "CommitEntryAction": [
        # termsGrowMonotonically,
        primaryHasEntriesItCreated_adr,
        # logEntryInTermImpliesSafeAtTerms
    ],
    "GetEntriesAction": [
        # termsGrowMonotonically,
        uniformLogEntriesInTerm_adr
    ]
}


committedEntryExistsOnQuorum_adr = StructuredProofNode("CommittedEntryExistsOnQuorum", "H_CommittedEntryExistsOnQuorum")
committedEntryExistsOnQuorum_adr.children = {
    "RollbackEntriesAction":[
        # lemmaTRUE,
        # StructuredProofNode("LogsLaterThanCommittedMustHaveCommitted", "H_LogsLaterThanCommittedMustHaveCommitted", children = [lemmaTRUE]),
        # StructuredProofNode("LeaderCompletenessLemma", "LeaderCompleteness", children = [lemmaTRUE])
        # primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted,

        # logsLaterThanCommittedMustHaveCommitted,

        primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted_adr

        # leaderCompleteness
    ]
}

activeConfigsOverlapWithCommittedEntry_adr.children = {
    "RollbackEntriesAction": [
        primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted_adr
    ]
}


adr_children = {
    "CommitEntryAction": [
        activeConfigsOverlapWithCommittedEntry_adr,
        newerConfigsDisablePrimaryCommitsInOlderTerms_adr,
        configsNonEmpty_adr
        # primaryConfigTermEqualToCurrentTerm_adr
    ]
}

# AbstractDynamicRaft proof structure.
adr_root = StructuredProofNode("Safety", "StateMachineSafety", children = adr_children)
adr_nodes = []
adr_actions = [
    "ClientRequestAction",
    "GetEntriesAction",
    "RollbackEntriesAction",
    "BecomeLeaderAction",
    "CommitEntryAction",
    "UpdateTermsActions",
    "ReconfigAction",
    "SendConfigAction"
]