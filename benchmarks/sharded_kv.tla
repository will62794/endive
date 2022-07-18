---- MODULE sharded_kv ----
EXTENDS TLC, Randomization

CONSTANT Key
CONSTANT Value
CONSTANT Node

CONSTANT Nil

\* The key-value store state on each node.
VARIABLE table

\* The set of keys owned by each node.
VARIABLE owner

\* The set of active transfer messages.
VARIABLE transfer_msg

vars == <<table, owner, transfer_msg>>

Reshard(k,v,n_old,n_new) ==
    /\ table[n_old][k] = v
    /\ table' = [table EXCEPT ![n_old][k] = Nil]
    /\ owner' = [owner EXCEPT ![n_old] = owner[n_old] \ {k}]
    /\ transfer_msg' = transfer_msg \cup {<<n_new,k,v>>}

RecvTransferMsg(n, k, v) ==
    /\ <<n,k,v>> \in transfer_msg
    /\ transfer_msg' = transfer_msg \ {<<n,k,v>>}
    /\ table' = [table EXCEPT ![n][k] = v]
    \* Become the owner of this key.
    /\ owner' = [owner EXCEPT ![n] = owner[n] \cup {k}]

Put(n, k, v) == 
    /\ k \in owner[n]
    /\ table' = [table EXCEPT ![n][k] = v]
    /\ UNCHANGED <<owner, transfer_msg>>

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)

Init == 
    /\ table = [n \in Node |-> [k \in Key |-> Nil]]
    \* Each node owns some subset of keys, and different nodes
    \* can't own the same key.
    /\ owner \in [Node -> SUBSET Key]
    /\ \A i,j \in Node : \A k \in Key : (k \in owner[i] /\ k \in owner[j]) => (i=j)
    /\ transfer_msg = {}

TypeOK ==
    /\ table \in [Node -> [Key -> Value \cup {Nil}]]
    /\ owner \in [Node -> SUBSET Key]
    /\ transfer_msg \in SUBSET (Node \times Key \times Value)

TypeOKRandom == 
    /\ owner \in [Node -> SUBSET Key]
    /\ table \in [Node -> [Key -> Value \cup {Nil}]]
    /\ transfer_msg \in RandomSetOfSubsets(150, 5, (Node \times Key \times Value))

\* Keys unique.
Safety == 
    \A n1,n2 \in Node, k \in Key, v1,v2 \in Value : 
        (table[n1][k]=v1 /\ table[n2][k]=v2) => (n1=n2 /\ v1=v2)

Symmetry == Permutations(Key) \cup Permutations(Value) \cup Permutations(Node)

NextUnchanged == UNCHANGED vars

====