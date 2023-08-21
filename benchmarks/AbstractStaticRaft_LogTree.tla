---- MODULE AbstractStaticRaft_LogTree ----

EXTENDS AbstractStaticRaft, FiniteSetsExt, Json, IOUtils

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)

\* Set of all subsets of a set of size <= k.
kOrSmallerSubset(k, S) == UNION {(kSubset(n, S)) : n \in 0..k}

\***************************************
\* Tree-based specification of Raft logs.
\***************************************

\* Last term of a sequence, or -1 if the sequence is empty.
SeqLastTerm(seq) == IF Len(seq) = 0 THEN -1 ELSE seq[Len(seq)][2]

\* Is a given section of log monotonically increasing.
IsMonotonic(seq) == \A i,j \in DOMAIN seq : i > j => seq[i] >= seq[j]

\* Max branching factor of global log "tree".
MaxBranchingFactor == 2

\* Max length of any log section.
MaxLogSectionLen == 1

\* All bounded size chunks of a log, which must be monotonic in terms and have indices
\* that increase strictly by 1.
LogSections == {
    seq \in BoundedSeq(LogIndices \X Terms, MaxLogSectionLen) : 
        \* Terms are monotonic.
        /\ IsMonotonic([i \in DOMAIN seq |-> seq[i][2]])
        \* Log indices increment strictly by 1.
        /\ \A i,j \in DOMAIN seq : (i = j + 1) => seq[j][1] = (seq[i][1] + 1)
}

\* Represent an edge in the tree as a log section and its corresponding 
\* set of "children" log sections.
TreeEdgeType == [
    log : LogSections, 
    children: kOrSmallerSubset(MaxBranchingFactor, LogSections)
]

\* The set of all valid tree "edges", where an edge is represented as a log
\* section and a set of children log sections.
ValidTreeEdges == {
    e \in TreeEdgeType : 
        \* Assume log sections are always non-empty.
        /\ e.log # <<>> /\ <<>> \notin e.children

        \* All children must maintain global monotonicity property i.e.
        \* all children logs are >= any terms in root log.
        /\ (\A c \in e.children : \A i \in DOMAIN c : c[i][2] >= SeqLastTerm(e.log))

        \* All children must start at the immediate next index from the end of this log section.
        /\ \A c \in e.children : c[1][1] = e.log[Len(e.log)][1] + 1

        \* Branch points in Raft have a particular property i.e. they can only
        \* occur when there are conflicting primaries in different terms. Thus, 
        \* it must be the case that all initial terms on any branch are different.
        \* At most one branch can be the one that continues the parent branch.
        /\ \A c1,c2 \in e.children : c1 # c2 => c1[1][2] # c2[1][2]

        \* Bound global depth of logs.
        /\ \A i \in DOMAIN e.log : e.log[i][1] <= MaxLogLen
        /\ \A c \in e.children : \A i \in DOMAIN c : c[i][1] <= MaxLogLen
}

ValidTreesBounded == {
    edges \in kOrSmallerSubset(2, ValidTreeEdges) :
        \* Ignore the empty tree.
        /\ edges # {}
        \* Assume log sections are uniquely represented in the tree.
        /\ \A e1,e2 \in edges : e1.log = e2.log => e1 = e2
        \* Root log entry must exist.
        /\ \E e \in edges : e.log[1] = <<1,0>>
        \* Assume for now that the root log entry <<1,0>> is unique (i.e. present on all nodes at initialization.)
        /\ \A e \in edges : (e.log[1][1] = 1) => (e.log[1] = <<1,0>>)
        \* Each node must have a valid parent, unless the node is the root.
        /\ \A e \in edges : 
            (\/ e.log[1] = <<1,0>> \* it is the root node.
             \/ \E epar \in edges : \E c \in epar.children : c[Len(c)] = e.log[1])
}

\* TODO: Invariant that checks whether all logs currently in the system correspond to 
\* some path in a valid log tree.
LogsAreValidTrees == TRUE

ASSUME PrintT(ValidTreeEdges)
ASSUME PrintT(Cardinality(ValidTreeEdges))


TreeAsEdgeSet(t) == 
    { {<<ToString(e.log),ToString(c)>> : c \in e.children} : e \in t}

ValidTreesAsEdgeSets == 
    {UNION TreeAsEdgeSet(t) : t \in ValidTreesBounded}

edgesJson == "{ \"edges\": " \o ToJson(ValidTreesAsEdgeSets) \o "}"
ASSUME PrintT(ValidTreesAsEdgeSets)

\* Serialize edge sets to JSON.
file == "edges.json"
opts == [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]
TXTSerializeResult == Serialize(edgesJson, file, opts)


\* 
\* Export sampling of valid trees in DOT graph format.
\* 
EdgeToDOTEdges(e) == 
    {ToString(e.log) \o " -> " \o ToString(c) : c \in e.children}

ASSUME PrintT("ValidTreesBounded")
ASSUME(PrintT(ValidTreesBounded))

ASSUME PrintT("Num ValidTreesBounded")
ASSUME(PrintT(Cardinality(ValidTreesBounded)))

DOTEdges == {UNION {EdgeToDOTEdges(e) : e \in t} : t \in ValidTreesBounded}

\* edgesJson == "{ \"edges\": " \o ToJson(DOTEdges) \o "}"


=============================================================================
