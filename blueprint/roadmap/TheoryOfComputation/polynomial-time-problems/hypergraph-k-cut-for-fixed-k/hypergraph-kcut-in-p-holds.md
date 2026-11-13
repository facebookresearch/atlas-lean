# Hypergraph $k$-cut for fixed $k$ is in P

For every natural number $k$, the decision version
of hypergraph $k$-cut is in the complexity class P. That problem accepts a hypergraph on the
vertices $0, \dots, n-1$, given by hyperedges with natural-number costs, and a budget $B$ iff every
hyperedge lists only vertices below $n$ and some partition of the vertices into $k$ non-empty parts
has total cost of the hyperedges meeting two parts at most $B$; inputs that do not decode are
rejected.

Chandrasekaran and Chekuri give, for every fixed $k$, a deterministic polynomial-time algorithm for
hypergraph $k$-cut with non-negative hyperedge costs, which decides this problem.

## Sources

- EGRES Open (Egerváry Research Group), list of open problems, Minimum k-way cut in a hypergraph, https://oldlemon.cs.elte.hu/egres/open/Minimum_k-way_cut_in_a_hypergraph; resolution: K. Chandrasekaran and C. Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, FOCS 2020; arXiv:2009.12442, abstract: for hypergraphs with non-negative hyperedge costs and fixed k, a deterministic polynomial-time algorithm for Hypergraph-k-cut (a least-cost F ⊆ E such that G - F has at least k components, equivalently a partition of V into k non-empty parts minimizing the cost of crossing hyperedges), https://arxiv.org/abs/2009.12442.
