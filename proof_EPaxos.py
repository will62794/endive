from proofs import *

#
# EPaxos proof structure.
#


def make_node(expr):
    return StructuredProofNode(expr[2:], expr)

lemmaTRUE = StructuredProofNode("LemmaTrue", "TRUE")
lemmaTRUEShim = StructuredProofNode("LemmaTrueShim", "1=1")


safety = make_node("H_Consistency")
safety.children = {}

root = safety
nodes = [

]
actions = [
    "ProposeAction",
    "Phase1FastAction",
    "Phase1SlowAction",
    "Phase2FinalizeAction",
    "FinalizeTryPreAcceptAction",
    "Phase1ReplyAction",
    "Phase2ReplyAction",
    "CommitAction",
    "SendPrepareAction",
    "ReplyPrepareAction",
    "PrepareFinalizeAction",
    "ReplyTryPreacceptAction"
]
