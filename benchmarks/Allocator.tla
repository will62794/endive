---------------------- MODULE Allocator-------------------
(***********************************************************************)
(* Specification of an allocator managing a set of resources:          *)
(* - Clients can request sets of resources whenever all their previous *)
(*   requests have been satisfied.                                     *)
(* - Requests can be partly fulfilled, and resources can be returned   *)
(*   even before the full request has been satisfied. However, clients *)
(*   only have an obligation to return resources after they have       *)
(*   obtained all resources they requested.                            *)
(* This allocator operates by repeatedly choosing a schedule according *)
(* to which requests are satisfied. Resources can be allocated out of  *)
(* order as long as no client earlier in the schedule asks for them.   *)
(* This module adds communication between the allocator and the client *)
(* processes, which now hold some local state.                         *)
(***********************************************************************)

\* Spec source: https://github.com/tlaplus/Examples/blob/master/specifications/allocator/AllocatorImplementation.tla

EXTENDS FiniteSets, Sequences, Naturals, TLC, Randomization

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME
  IsFiniteSet(Resources)

VARIABLES
  (** variables held by the allocator **)
  unsat,       \* set of all outstanding requests per process
  alloc,       \* set of resources allocated to given process
  sched,       \* schedule represented as a sequence of clients
  (** variables of the clients **)
  requests,    \* pending requests per client
  holding,     \* resources currently held by the client
  (** communication network between clients and allocator **)
  network,      \* set of messages in transit
  allocMsgs,
  requestMsgs

\* Sched == INSTANCE SchedulingAllocator

-------------------------------------------------------------------------

(* Range of a function, e.g. elements of a sequence *)
Range(f) == { f[x] : x \in DOMAIN f }

(* The set of permutations of a finite set, represented as sequences.  *)
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
       IF ss = {} THEN { << >> }
       ELSE LET ps == [ x \in ss |-> 
                        { Append(sq,x) : sq \in perms[ss \ {x}] } ]
            IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

(* Resources are available iff they have not been allocated. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(* Clients with pending requests that have not yet been scheduled *)
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

(* Remove element at index i from a sequence.                          *)
(* Assumes that i \in 1..Len(seq)                                      *)
Drop(seq,i) == SubSeq(seq, 1, i-1) \circ SubSeq(seq, i+1, Len(seq))

Messages ==
  [type : {"request", "allocate", "return"}, 
   clt : Clients,
   rsrc : SUBSET Resources]

RequestMessages ==
  [type : {"request"}, 
   clt : Clients,
   rsrc : SUBSET Resources]

AllocateMessages ==
  [type : {"allocate"}, 
   clt : Clients,
   rsrc : SUBSET Resources]

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

TypeOK ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in SUBSET Messages
  /\ requestMsgs \in SUBSET RequestMessages
  /\ allocMsgs \in SUBSET AllocateMessages

TypeOKRandom ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in BoundedSeq(Clients, 3)
  /\ requests \in [Clients -> SUBSET Resources]
  /\ holding \in [Clients -> SUBSET Resources]
  /\ network \in RandomSetOfSubsets(4, 2, Messages)
  /\ requestMsgs \in RandomSetOfSubsets(4, 2, RequestMessages)
  /\ allocMsgs \in RandomSetOfSubsets(4, 2, AllocateMessages)
-------------------------------------------------------------------------

(* Initially, no resources have been requested or allocated. *)
Init == 
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>
  /\ requests = [c \in Clients |-> {}]
  /\ holding = [c \in Clients |-> {}]
  /\ network = {}
  /\ requestMsgs = {}
  /\ allocMsgs = {}

(* A client c may request a set of resources provided that it has      *)
(* neither pending requests nor holds any resources. The request is    *)
(* put into the network for delivery to the allocator.                 *)
Request(c,S) ==
  /\ requests[c] = {} /\ holding[c] = {}
  /\ S # {} /\ requests' = [requests EXCEPT ![c] = S]
  /\ requestMsgs' = requestMsgs \cup {[type |-> "request", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat,alloc,sched,holding, network, allocMsgs>>

(* Reception of a request message from a client by the allocator.      *)
(* The allocator updates its data structures and inserts the client    *)
(* into the pool of clients with pending requests.                     *)
RReq(m) ==
  /\ m \in requestMsgs /\ m.type = "request"
  /\ alloc[m.clt] = {}   \** don't handle request messages prematurely(!)
  /\ unsat' = [unsat EXCEPT ![m.clt] = m.rsrc]
  /\ requestMsgs' = requestMsgs \ {m}
  /\ UNCHANGED <<alloc,sched,requests,holding, network, allocMsgs>>

(* Allocation of a set of available resources to a client that has     *)
(* requested them (the entire request does not have to be filled).     *)
(* The process must appear in the schedule, and no process earlier in  *)
(* the schedule may have requested one of the resources.               *)
Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched,i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ allocMsgs' = allocMsgs \cup {[type |-> "allocate", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<requests,holding, requestMsgs, network>>

(* Reception of an allocation message by a client.                     *)
RAlloc(m) ==
  /\ m \in allocMsgs /\ m.type = "allocate"
  /\ holding' = [holding EXCEPT ![m.clt] = @ \cup m.rsrc]
  /\ requests' = [requests EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ allocMsgs' = allocMsgs \ {m}
  /\ UNCHANGED <<unsat,alloc,sched, requestMsgs, network>>

(* Client c returns a set of resources that it holds. It may do so     *)
(* even before its full request has been honored.                      *)
Return(c,S) ==
  /\ S # {} /\ S \subseteq holding[c]
  /\ holding' = [holding EXCEPT ![c] = @ \ S]
  /\ network' = network \cup {[type |-> "return", clt |-> c, rsrc |-> S]}
  /\ UNCHANGED <<unsat,alloc,sched,requests, requestMsgs, allocMsgs>>

(* Reception of a return message by the allocator.                     *)
RRet(m) ==
  /\ m \in network /\ m.type = "return"
  /\ alloc' = [alloc EXCEPT ![m.clt] = @ \ m.rsrc]
  /\ network' = network \ {m}
  /\ UNCHANGED <<unsat,sched,requests,holding, requestMsgs, allocMsgs>>

(* The allocator extends its schedule by adding the processes from     *)
(* the pool (that have outstanding requests but that have not yet been *)
(* scheduled, in some unspecified order.                               *)
Schedule == 
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \circ sq
  /\ UNCHANGED <<unsat,alloc,requests,holding,network,requestMsgs, allocMsgs>>

RequestAction == \E c \in Clients, S \in SUBSET Resources : Request(c,S) 
AllocateAction == \E c \in Clients, S \in SUBSET Resources : Allocate(c,S)
ReturnAction == \E c \in Clients, S \in SUBSET Resources : Return(c,S)
RReqAction == \E m \in requestMsgs : RReq(m)
RAllocAction == \E m \in allocMsgs : RAlloc(m)
RRetAction == \E m \in network : RRet(m)
ScheduleAction == Schedule

(* The next-state relation per client and set of resources.            *)
\* Next ==
\*     \/ \E c \in Clients, S \in SUBSET Resources : Request(c,S) 
\*     \/ \E c \in Clients, S \in SUBSET Resources : Allocate(c,S)
\*     \/ \E c \in Clients, S \in SUBSET Resources : Return(c,S)
\*     \/ \E m \in network : RReq(m)
\*     \/ \E m \in network : RAlloc(m)
\*     \/ \E m \in network : RRet(m)
\*     \/ Schedule

Next ==
    \/ RequestAction
    \/ AllocateAction
    \/ ReturnAction
    \/ RReqAction
    \/ RAllocAction
    \/ RRetAction
    \/ ScheduleAction

vars == <<unsat,alloc,sched,requests,holding,network,requestMsgs,allocMsgs>>

-------------------------------------------------------------------------

(***********************************************************************)
(* Liveness assumptions:                                               *)
(* - Clients must return resources if their request has been satisfied.*)
(* - The allocator must eventually allocate resources when possible.   *)
(* - The allocator must schedule the processes in the pool.            *)
(* - Messages must eventually be received.                             *)
(***********************************************************************)

Liveness ==
  /\ \A c \in Clients : WF_vars(requests[c]={} /\ Return(c,holding[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)
  /\ \A m \in Messages : 
       /\ WF_vars(RReq(m))
       /\ WF_vars(RAlloc(m))
       /\ WF_vars(RRet(m))

(* The specification of the entire system *)
Specification == Init /\ [][Next]_vars /\ Liveness

-------------------------------------------------------------------------

UnscheduledClients ==    \** clients that do not appear in the schedule
  Clients \ Range(sched)

PrevResources(i) ==
  \** resources that will be available when client i has to be satisfied
  available
  \cup (UNION {unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..i-1})
  \cup (UNION {alloc[c] : c \in UnscheduledClients})

RequestsInTransit(c) ==  \** requests sent by c but not yet received
  { msg.rsrc : msg \in {m \in requestMsgs : m.type = "request" /\ m.clt = c} }

AllocsInTransit(c) ==  \** allocations sent to c but not yet received
  { msg.rsrc : msg \in {m \in network : m.type = "allocate" /\ m.clt = c} }

ReturnsInTransit(c) ==  \** return messages sent by c but not yet received
  { msg.rsrc : msg \in {m \in network : m.type = "return" /\ m.clt = c} }

AllocatorInvariant ==  \** a lower-level invariant
  /\ \** all clients in the schedule have outstanding requests
     \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \** all clients that need to be scheduled have outstanding requests
     \A c \in toSchedule : unsat[c] # {}
  /\ \** clients never hold a resource requested by a process earlier
     \** in the schedule
     \A i \in DOMAIN sched : \A j \in 1..i-1 : 
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  /\ \** the allocator can satisfy the requests of any scheduled client
     \** assuming that the clients scheduled earlier release their resources
     \A i \in DOMAIN sched : unsat[sched[i]] \subseteq PrevResources(i)

Invariant ==  \** a lower-level invariant
  (** invariants for the allocator's data structures as before **)
  /\ AllocatorInvariant
  (** interplay between allocator and client variables **)
  /\ \A c \in Clients : 
       /\ Cardinality(RequestsInTransit(c)) <= 1
       /\ requests[c] = unsat[c]
                     \cup UNION RequestsInTransit(c)
                     \cup UNION AllocsInTransit(c)
       /\ alloc[c] = holding[c] 
                  \cup UNION AllocsInTransit(c) 
                  \cup UNION ReturnsInTransit(c)

(* correctness properties in terms of clients' variables *)
H_ResourceMutex ==
  \A c1,c2 \in Clients : holding[c1] \cap holding[c2] # {} => c1 = c2

ClientsWillReturn ==
  \A c \in Clients: (requests[c]={} ~> holding[c]={})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in requests[c] ~> r \in holding[c]

InfOftenSatisfied == 
  \A c \in Clients : []<>(requests[c] = {})


NextUnchanged == UNCHANGED vars
CTICost == 0


H_Inv1_R0_0_I1 == \A VARCI \in Clients : (holding[VARCI] = {})

-------------------------------------------------------------------------

\* THEOREM Specification => []TypeInvariant
\* THEOREM Specification => []ResourceMutex
\* THEOREM Specification => []Invariant
\* THEOREM Specification => ClientsWillReturn
\* THEOREM Specification => ClientsWillObtain
\* THEOREM Specification => InfOftenSatisfied

-------------------------------------------------------------------------

(* This implementation is a refinement of the scheduling allocator.    *)

\* SchedAllocator == Sched!Allocator
\* THEOREM Specification => SchedAllocator
=========================================================================
