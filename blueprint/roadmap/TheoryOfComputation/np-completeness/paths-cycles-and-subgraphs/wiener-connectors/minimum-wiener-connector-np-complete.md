# MINIMUM WIENER CONNECTOR is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a connected simple graph $G$ on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, a list $Q$ of distinct query vertices and a positive integer $K$, decide whether some vertex set $S \supseteq Q$ induces a connected subgraph in which the sum of the distances over all unordered pairs of vertices of $S$ is at most $K$.

## Sources

- N. Ruchansky, F. Bonchi, D. García-Soriano, F. Gullo and N. Kourtellis, "The minimum Wiener connector problem", in *Proceedings of the 2015 ACM SIGMOD International Conference on Management of Data* (2015), 1587-1602, doi:10.1145/2723372.2749449 (Problem 1 and Theorem 2; arXiv:1504.00513).
