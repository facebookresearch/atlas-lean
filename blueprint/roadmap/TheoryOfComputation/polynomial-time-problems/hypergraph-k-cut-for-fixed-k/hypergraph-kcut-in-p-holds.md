# Hypergraph $k$-cut for fixed $k$ is in P

For every natural number $k$, the decision version
of hypergraph $k$-cut is in the complexity class P. That problem accepts a hypergraph on the
vertices $0, \dots, n-1$, given by hyperedges with natural-number costs, and a budget $B$ iff every
hyperedge lists only vertices below $n$ and some partition of the vertices into $k$ non-empty parts
has total cost of the hyperedges meeting two parts at most $B$; inputs that do not decode are
rejected.

Chandrasekaran and Chekuri give, for every fixed $k$, a deterministic polynomial-time algorithm for
hypergraph $k$-cut with non-negative hyperedge costs, which decides this problem. Since $n$ is written
in binary, the instance is first compacted, after checking that every hyperedge lists only vertices
below $n$. For $k = 0$ the answer is yes exactly when $n = 0$. For $k \ge 1$, the $I$ vertices on no
hyperedge cost nothing and are interchangeable, so keeping the vertices on hyperedges and
$\min(k, I)$ of the others, renumbered, preserves the existence of a partition into $k$ non-empty
parts of cost at most $B$, and leaves a number of vertices polynomial in the input length.

## Sources

- EGRES Open (Egerváry Research Group), list of open problems, Minimum k-way cut in a hypergraph, https://oldlemon.cs.elte.hu/egres/open/Minimum_k-way_cut_in_a_hypergraph; resolution: Karthekeyan Chandrasekaran and Chandra Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, FOCS 2020; arXiv:2009.12442, abstract: for hypergraphs with non-negative hyperedge costs and fixed k, a deterministic polynomial-time algorithm for Hypergraph-k-cut (a least-cost F ⊆ E such that G - F has at least k components, equivalently a partition of V into k non-empty parts minimizing the cost of crossing hyperedges), https://arxiv.org/abs/2009.12442.
