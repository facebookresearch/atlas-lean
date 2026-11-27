# OMv-hardness of dynamic subgraph connectivity

Consider fully dynamic subgraph connectivity on a graph with $n$ vertices and $m$ edges, as defined on [dynamic graph problems](dynamic-graph-problems.md): vertices are switched on and off, and queries ask whether two vertices are connected through switched-on vertices.

**Theorem (Henzinger, Krinninger, Nanongkai, Saranurak).** Assume the [OMv conjecture](the-online-matrix-vector-multiplication.md), and let $0 \le \alpha \le 1$ and $\varepsilon > 0$ be constants.
1. No algorithm for subgraph connectivity with polynomial preprocessing time has both amortized update time $O(m^{\alpha - \varepsilon})$ and amortized query time $O(m^{1 - \alpha - \varepsilon})$. For $0 < \alpha < 1$ this holds on graphs with $m \le \min\{n^{1/\alpha}, n^{1/(1-\alpha)}\}$; for $\alpha \in \{0, 1\}$ it holds on graphs with $m \le n$. It holds also for algorithms whose queries err with probability at most $1/3$.
2. In terms of $n$, on graphs with $m = \Theta(n^2)$, no such algorithm has both update time $O(n^{1 - \varepsilon})$ and query time $O(n^{2 - \varepsilon})$.

For $\alpha = 2/3$, part 1 matches the known algorithm with amortized update time $\tilde O(m^{2/3})$ and query time $\tilde O(m^{1/3})$. Part 2 matches the algorithm with $\tilde O(n)$ update time and $O(1)$ query time.

**Proof idea.** The OMv conjecture implies the same truly-subcubic hardness for the online vector-matrix-vector problem *OuMv*: an OMv algorithm can be simulated with OuMv queries. In OuMv, the matrix $M$ is fixed, pairs of vectors $(u_i, v_i)$ arrive online, and the algorithm must output the single bit $u_i^\top M v_i$. An OuMv instance becomes a subgraph-connectivity instance as follows:
- encode $M$ as a bipartite graph between two copies of the index set;
- attach a source to the left copy and a sink to the right copy;
- for each pair $(u_i, v_i)$, switch on exactly the left vertices in the support of $u_i$ and the right vertices in the support of $v_i$, switching off every vertex that was on in the previous round but is not in the new supports, with at most $O(n)$ updates per round, then ask one connectivity query.

The bit $u_i^\top M v_i$ is $1$ exactly when the source and sink are connected. Faster updates and queries would therefore give a truly subcubic algorithm for OuMv, and so for OMv.

## Depends on

- [The online matrix-vector multiplication conjecture](the-online-matrix-vector-multiplication.md)
- [Dynamic graph problems](dynamic-graph-problems.md)

## Sources

- M. Henzinger, S. Krinninger, D. Nanongkai and T. Saranurak, "Unifying and strengthening hardness for dynamic problems via the online matrix-vector multiplication conjecture", *Proceedings of the 47th ACM STOC*, 2015, arXiv:1511.06773, <https://arxiv.org/abs/1511.06773>:
    - Section 1.1: the subgraph-connectivity lower bound with polynomial preprocessing time, amortized update time $m^{\alpha - \varepsilon}$ and query time $m^{1 - \alpha - \varepsilon}$ for $0 \le \alpha \le 1$, its range $m \le \min\{n^{1/\alpha}, n^{1/(1-\alpha)}\}$ (footnote 4), and the matching upper bounds;
    - the summary table: the row with update time $n^{1-\varepsilon}$ and query time $n^{2-\varepsilon}$ for $m = \Theta(n^2)$;
    - Section 2: $\gamma$-OMv (Definition 2.1), $\gamma$-OuMv (Definition 2.6), and the reduction from OMv to OuMv.
