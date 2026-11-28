# RURAL POSTMAN is NP-complete

The RURAL POSTMAN decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The decision problem accepts exactly the encodings of the following yes-instances. Instance: a simple graph $G = (V, E)$ on $V = \{0, \dots, n - 1\}$, a length $l(e) \in \mathbb N$ for each $e \in E$, a subset $E' \subseteq E$ of required edges, and a positive integer $B$. Question: is there a closed walk in $G$ that traverses every edge of $E'$ at least once and has total length at most $B$? The walk may repeat vertices and edges, and its length counts the length of an edge once per traversal: a single required bridge of length $1$ is covered by walking across it and back, at total length $2$. When $E'$ is empty, the walk with no edges at any vertex qualifies; the graph with no vertices has no closed walk.

The exact conditions are those of [well-formedness](well-formed.md) and [feasibility](rural-postman-feasible.md). Numbers are encoded in binary, the edges as a list of endpoint pairs with lengths and the required edges as a list of endpoint pairs.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN.
- J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems", Networks 6 (1976), 273-280, doi:10.1002/net.3230060305 (Theorem: the rural postman problem is polynomial complete for undirected and for directed graphs).
