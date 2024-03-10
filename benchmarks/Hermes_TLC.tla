------------------------------- MODULE Hermes_TLC -------------------------------
\* 
\* Spec source: https://github.com/ease-lab/Hermes
\* 

EXTENDS Hermes, Randomization, TLC

\* 
\* Try to work around large message types here by using randomized message set definitions.
\* 

\* Set of all subsets of a set of size <= k.
\* kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

INVMessageRandom(r) == [
    type       |-> "INV", 
    sender     |-> RandomElement(H_NODES),
    epochID    |-> RandomElement(0..(Cardinality(H_NODES) - 1)),
    version    |-> RandomElement(0..H_MAX_VERSION),  
    tieBreaker |-> RandomElement(H_NODES)
]

ACKMessageRandom(r) == [
    type       |-> "ACK", 
    sender     |-> RandomElement(H_NODES),
    epochID    |-> RandomElement(0..(Cardinality(H_NODES) - 1)),
    version    |-> RandomElement(0..H_MAX_VERSION),  
    tieBreaker |-> RandomElement(H_NODES)
]

VALMessageRandom(r) == [
    type |-> "VAL",        \* optimization: epochID is not required for VALs
                          \* epochID   : 0..(Cardinality(H_NODES) - 1),
    version    |-> RandomElement(0..H_MAX_VERSION), 
    tieBreaker |-> RandomElement(H_NODES)    
]

TypeOKRandom ==  \* The type correctness invariant
    /\ msgsINV \in SUBSET {INVMessageRandom(0),INVMessageRandom(0)}
    /\ msgsVAL \in SUBSET {VALMessageRandom(0),VALMessageRandom(0)}
    /\ msgsACK \in SUBSET {ACKMessageRandom(0),ACKMessageRandom(0)}
    /\ nodeRcvedAcks \in [H_NODES -> SUBSET H_NODES]
    /\ \A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n})
    /\  nodeLastWriter  \in [H_NODES -> H_NODES]
    /\  nodeLastWriteTS \in [H_NODES -> [version : 0..H_MAX_VERSION, tieBreaker: H_NODES ]]
    /\  nodeTS          \in [H_NODES -> [version : 0..H_MAX_VERSION, tieBreaker: H_NODES ]]
    /\  nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write", "write", "replay"}]
    \*  membership and epoch id related
    /\  aliveNodes      \in SUBSET H_NODES
    /\  epochID         \in 0..(Cardinality(H_NODES) - 1)
    /\  nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)]

CTICost == Cardinality(msgsINV \cup msgsVAL \cup msgsACK) + Cardinality(aliveNodes)

=============================================================================
