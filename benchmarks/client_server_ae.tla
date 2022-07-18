---- MODULE client_server_ae ----
\* benchmark: pyv-client-server-ae

EXTENDS TLC

CONSTANT Node
CONSTANT Request
CONSTANT Response

VARIABLE match

VARIABLE request_sent
VARIABLE response_sent
VARIABLE response_received

vars == <<match,request_sent,response_sent,response_received>>

ResponseMatched(n,p) == \E r \in Request : (<<n,r>> \in request_sent) /\ <<r,p>> \in match

NewRequest(n, r) ==
    /\ request_sent' = request_sent \cup {<<n,r>>}
    /\ UNCHANGED <<response_sent,response_received,match>>

Respond(n,r,p) ==
    /\ <<n,r>> \in request_sent
    /\ <<r,p>> \in match
    /\ response_sent' = response_sent \cup {<<n,p>>}
    /\ UNCHANGED <<request_sent,response_received,match>>

ReceiveResponse(n,p) == 
    /\ <<n,p>> \in response_sent
    /\ response_received' = response_received \cup {<<n,p>>}
    /\ UNCHANGED <<request_sent,response_sent,match>>

Next ==
    \/ \E n \in Node, r \in Request : NewRequest(n,r)
    \/ \E n \in Node, r \in Request, p \in Response : Respond(n,r,p)
    \/ \E n \in Node, p \in Response : ReceiveResponse(n,p)

Init == 
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent = {}
    /\ response_sent = {}
    /\ response_received = {}

TypeOK ==
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent \in SUBSET (Node \X Request)
    /\ response_sent \in SUBSET (Node \X Response)
    /\ response_received \in SUBSET (Node \X Response)

NextUnchanged == UNCHANGED vars

Safety == \A n \in Node, p \in Response : (<<n,p>> \in response_received) => ResponseMatched(n,p)

Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response)

====