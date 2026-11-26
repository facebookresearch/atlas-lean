# Korhonen–Lokshtanov: a (1+ε)-approximation for treewidth in time k^{O(k/ε)} n^{O(1)}

There is an algorithm that, given an $n$-vertex graph $G$, an integer $k$ and a rational $\varepsilon\in(0,1)$, in time $k^{O(k/\varepsilon)}\,n^{O(1)}$ either outputs a tree decomposition of $G$ of width at most $(1+\varepsilon)k$ or determines that $\operatorname{tw}(G) > k$. Before this result, no FPT-approximation algorithm with ratio below 2 was known other than the exact algorithms; the algorithm uses polynomial space.

## Proof sketch

The same local-improvement framework as for the exact algorithm is run with a relaxed target width $(1+\varepsilon)k$; the slack allows a coarser enumeration of split configurations, in which only $O(k/\varepsilon)$ "heavy" pieces have to be guessed among $k^{O(1)}$ options each, giving the $k^{O(k/\varepsilon)}$ factor.

## Depends on

- [FPT-approximation algorithms for treewidth](fpt-approximation-algorithms-for-treewidth.md)

## Proof depends on

- [Korhonen–Lokshtanov: exact treewidth in time 2^{O(k^2)} n^{O(1)}](korhonen-lokshtanov-exact-treewidth.md)

## Sources

- Tuukka Korhonen and Daniel Lokshtanov, "An Improved Parameterized Algorithm for Treewidth", STOC (2023), arXiv:2211.07154.
