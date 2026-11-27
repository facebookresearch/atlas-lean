# STACKER-CRANE PATH is NP-complete

The STACKER-CRANE PATH decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The decision problem accepts exactly the encodings of the following yes-instances. Instance: a mixed graph on $V = \{0, \dots, n - 1\}$ with a list $A$ of directed edges and a list $E$ of undirected edges, each joining two distinct vertices, no two directed edges with the same tail and head and no two undirected edges joining the same two vertices, a length $l(e) \in \mathbb N$ for each edge, and a positive integer bound $B$. Question: is there a walk, not necessarily closed and with no specified endpoints, that traverses every directed edge in $A$ at least once, in its specified direction, and has total length at most $B$? The walk is a sequence of [moves](moves.md), each traversing a directed edge from its tail to its head or an undirected edge in either direction, and each move starts where the previous one ends. It may repeat vertices and edges, and its length counts the length of an edge once per traversal. A walk has a start vertex even with no moves, so the graph must have at least one vertex: when $A$ is empty every instance with $n \ge 1$ qualifies, and the graph with no vertices never does.

The exact conditions are those of [well-formedness](../chinese-postman-for-mixed-graphs/well-formed.md) and [feasibility](stacker-crane-path-feasible.md). Numbers are encoded in binary.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE, comment (p. 213: "The analogous path problem (with or without specified endpoints) is also NP-complete").
- G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for some routing problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017 (the entry's reference for STACKER-CRANE).
