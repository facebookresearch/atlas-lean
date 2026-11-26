# K-Ramsey graphs and bipartite K-Ramsey graphs

A graph on $N$ vertices is *$K$-Ramsey* if it contains no clique and no independent set on $K$ vertices. A bipartite graph with sides of size $N$ is *bipartite $K$-Ramsey* if for all $S, T$ of size $K$ on the two sides, the induced bipartite subgraph on $S \times T$ is neither complete nor empty. A family of graphs is *explicit* if adjacency of two vertices given in binary is decidable in time $\mathrm{poly}(\log N)$. By Erdős's probabilistic argument, $K = 2\log_2 N$ is achieved by almost all graphs.

## Depends on

- [Diagonal Ramsey number of a graph](../../../GraphTheory/graph-ramsey-theory/graph-ramsey-numbers/diagonal-graph-ramsey.md)
- [Erdős's lower bound on $R(k, k)$](../../../GraphTheory/graph-ramsey-theory/graph-ramsey-numbers/lt-graph-ramsey-of-choose-mul-lt.md)

## Sources

- Paul Erdos, "Some remarks on the theory of graphs", Bulletin of the AMS 53 (1947).
- Eshan Chattopadhyay, David Zuckerman, "Explicit two-source extractors and resilient functions", Annals of Mathematics 189(3) (2019), STOC (2016); ECCC TR15-119.
