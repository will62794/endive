---- MODULE sharded_kv_no_lost_keys ----
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

vars == <<table,owner,transfer_msg>>

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
    /\ transfer_msg = {}
    \* Each node owns some subset of keys, and different nodes
    \* can't own the same key.
    /\ owner \in [Node -> SUBSET Key]
    /\ \A i,j \in Node : \A k \in Key : (k \in owner[i] /\ k \in owner[j]) => (i=j)
    \* No lost keys assumption: every key is owned by some node.
    /\ \A k \in Key : \E n \in Node : k \in owner[n]

TypeOK ==
    /\ table \in [Node -> [Key -> Value \cup {Nil}]]
    /\ owner \in [Node -> SUBSET Key]
    /\ transfer_msg \in SUBSET (Node \X Key \X Value)

TypeOKRandom == 
    /\ owner \in RandomSubset(35, [Node -> SUBSET Key])
    /\ table \in RandomSubset(35, [Node -> [Key -> Value \cup {Nil}]])
    /\ transfer_msg \in RandomSetOfSubsets(35, 6, (Node \times Key \times Value))

\* invariant [safety] (exists N,K,V. transfer_msg(N,K,V)) | (forall K. exists N. owner(N,K))
Safety == 
    \/ \E n \in Node, k \in Key, v \in Value : <<n,k,v>> \in transfer_msg 
    \/ \A k \in Key : \E n \in Node : k \in owner[n]

Symmetry == Permutations(Key) \cup Permutations(Value) \cup Permutations(Node)

NextUnchanged == UNCHANGED vars

====