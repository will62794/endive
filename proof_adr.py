from proofs import *


#
# AbstractDynamicRaft proof structure.
#

quorumsSafeAtTerms_adr = StructuredProofNode("QuorumsSafeAtTerms", "H_QuorumsSafeAtTerms")
quorumsSafeAtTerms_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"

primaryConfigTermEqualToCurrentTerm_adr = StructuredProofNode("PrimaryConfigTermEqualToCurrentTerm", "H_PrimaryConfigTermEqualToCurrentTerm")
primaryConfigTermEqualToCurrentTerm_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"

activeConfigsOverlap_adr = StructuredProofNode("ActiveConfigsOverlap", "H_ActiveConfigsOverlap")
activeConfigsSafeAtTerms_adr = StructuredProofNode("ActiveConfigsSafeAtTerms", "H_ActiveConfigsSafeAtTerms")

configVersionAndTermUnique_adr = StructuredProofNode("ConfigVersionAndTermUnique", "H_ConfigVersionAndTermUnique")
# configVersionAndTermUnique_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"
configVersionAndTermUnique_adr.ctigen_typeok = "TypeOK"
configVersionAndTermUnique_adr.children = {
    "BecomeLeaderAction":[
        primaryConfigTermEqualToCurrentTerm_adr,
        activeConfigsSafeAtTerms_adr
    ]
}


primaryInTermContainsNewestConfigOfTerm_adr = StructuredProofNode("PrimaryInTermContainsNewestConfigOfTerm", "H_PrimaryInTermContainsNewestConfigOfTerm")
# primaryInTermContainsNewestConfigOfTerm.ch

onePrimaryPerTerm_adr = StructuredProofNode("OnePrimaryPerTerm_Lemma", "H_OnePrimaryPerTerm", children = {
    # lemmaTRUE,
    "BecomeLeaderAction": [
        # quorumsSafeAtTerms_adr,
        primaryConfigTermEqualToCurrentTerm_adr,
        configVersionAndTermUnique_adr,
        # primaryInTermContainsNewestConfigOfTerm_adr,
        activeConfigsOverlap_adr,
        activeConfigsSafeAtTerms_adr
    ]
})
onePrimaryPerTerm_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"


primaryHasEntriesItCreated_adr = StructuredProofNode("PrimaryHasEntriesItCreated_A", "H_PrimaryHasEntriesItCreated")
primaryHasEntriesItCreated_adr.children = {
    "ClientRequestAction": [
        onePrimaryPerTerm_adr,
    ],
    "BecomeLeaderAction": [
        # quorumsSafeAtTerms,
        # logEntryInTermImpliesSafeAtTerms
    ]
}
primaryHasEntriesItCreated_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"



logMatching_adr = StructuredProofNode("LogMatching_Lemma", "LogMatching", children = {
    "ClientRequestAction":[primaryHasEntriesItCreated_adr]
})
logMatching_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"


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
uniformLogEntriesInTerm_adr.ctigen_typeok = "TypeOKRandomEmptyCommitted"


primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted_adr = StructuredProofNode("PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted", "H_PrimaryOrLogsLaterThanCommittedMustHaveEarlierCommitted")
primaryOrLogsLaterThanCommittedMustHaveEarlierCommitted_adr.children = {
    "BecomeLeaderAction": [
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm,
        # logEntryInTermImpliesSafeAtTerms,
        # committedEntryExistsOnQuorum_cycleBreak
    ],
    "ClientRequestAction": [
        # termsGrowMonotonically,
        # uniformLogEntriesInTerm,
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


adr_children = {
    "CommitEntryAction": [
        committedEntryExistsOnQuorum_adr,
        onePrimaryPerTerm_adr
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