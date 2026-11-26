# FPT-approximation algorithms for treewidth

An **$\alpha$-approximation algorithm for treewidth with running time $f(k)\cdot g(n)$** takes an $n$-vertex graph $G$ and an integer $k$ and, within that time, either outputs a tree decomposition of $G$ of width at most $\alpha(k)$, or correctly reports that $\operatorname{tw}(G) > k$. Constant-factor approximations with $f(k)=2^{O(k)}$ and $g(n)=n$ are the relevant regime for using treewidth as a preprocessing step for $2^{O(k)}n$-time dynamic programming. Exact computation of treewidth is NP-hard, and constant-factor polynomial-time approximation is unknown (it is ruled out under the Small Set Expansion Conjecture), so parameterized approximation is the natural model.

## Depends on

- [TREEWIDTH is NP-complete](../../../np-completeness/graph-coloring-and-partitioning/treewidth/treewidth-np-complete.md)
- [Fixed-parameter tractable problems](../../parameterized-complexity/fpt.md)
- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)

## Sources

- Hans L. Bodlaender, Pål Grønås Drange, Markus S. Dregi, Fedor V. Fomin, Daniel Lokshtanov and Michał Pilipczuk, "A c^k n 5-Approximation Algorithm for Treewidth", SIAM Journal on Computing 45(2) (2016), arXiv:1304.6321.
- Tuukka Korhonen, "A Single-Exponential Time 2-Approximation Algorithm for Treewidth", FOCS (2021), arXiv:2104.07463.
- Tuukka Korhonen and Daniel Lokshtanov, "An Improved Parameterized Algorithm for Treewidth", STOC (2023), arXiv:2211.07154.
