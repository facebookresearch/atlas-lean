# $k$-dimensional Weisfeiler–Leman refinement

For $k \ge 1$ and a finite graph $G = (V,E)$, the $k$-dimensional Weisfeiler–Leman algorithm ($k$-WL, in the Cai–Fürer–Immerman numbering) colors $k$-tuples. The initial color of $\bar u \in V^k$ is its atomic type (equalities and adjacencies among its entries). Then $c_{t+1}(\bar u) = \big(c_t(\bar u), \{\!\{ (\mathrm{atp}(\bar u w), c_t(\bar u[1/w]), \dots, c_t(\bar u[k/w])) : w \in V \}\!\}\big)$, where $\mathrm{atp}(\bar u w)$ is the atomic type of the $(k+1)$-tuple (redundant for $k\ge2$; for $k=1$ this is color refinement), where $\bar u[i/w]$ replaces the $i$-th entry by $w$. The partitions stabilize after at most $|V|^k$ rounds. Two graphs are *distinguished by $k$-WL* if the stable color histograms (multisets of colors of all $k$-tuples, computed jointly) differ.

## Depends on

- [Color refinement and the stable coloring](color-refinement-stable-coloring.md)

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
- N. Immerman and E. S. Lander, "Describing Graphs: A First-Order Approach to Graph Canonization", in Complexity Theory Retrospective, Springer, 59–81, 1990.
