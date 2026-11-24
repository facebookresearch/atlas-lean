# Decision version of hypergraph $k$-cut

For a natural number $k$, this is the decision
problem on bitstrings that decodes an input as a triple $(n, E, B)$: a number $n$ of vertices
$0, \dots, n-1$, a list $E$ of hyperedges, each a list of vertices with a natural-number cost, and
a natural-number budget $B$. It accepts the input iff every hyperedge lists only vertices below
$n$ and there is a partition of the vertices into $k$ non-empty parts, given by a map $f$ from
$\{0, \dots, n-1\}$ onto $\{0, \dots, k-1\}$, such that the total cost of the hyperedges in $E$
(counted with multiplicity) that meet two different parts is at most $B$. Inputs that do not
decode are rejected.
