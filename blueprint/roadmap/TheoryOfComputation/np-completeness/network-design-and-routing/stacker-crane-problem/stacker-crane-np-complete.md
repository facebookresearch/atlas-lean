# STACKER-CRANE is NP-complete

The STACKER-CRANE decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The decision problem accepts exactly the encodings of the following yes-instances. Instance: a mixed graph on $V = \{0, \dots, n - 1\}$ with a list $A$ of directed edges and a list $E$ of undirected edges, each joining two distinct vertices, no two directed edges with the same tail and head and no two undirected edges joining the same two vertices, a length $l(e) \in \mathbb N$ for each edge, and a positive integer bound $B$. Question: is there a closed walk that traverses every directed edge in $A$ at least once, in its specified direction, and has total length at most $B$? The walk is a sequence of [moves](moves.md), each traversing a directed edge from its tail to its head or an undirected edge in either direction, and each move starts where the previous one ends. It may repeat vertices and edges, and its length counts the length of an edge once per traversal. The last move ends where the first one starts. When $A$ is empty the walk with no moves qualifies, even on the graph with no vertices.

The exact conditions are those of [well-formedness](../chinese-postman-for-mixed-graphs/well-formed.md) and [feasibility](stacker-crane-feasible.md). Numbers are encoded in binary.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE.
- G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for some routing problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017.
