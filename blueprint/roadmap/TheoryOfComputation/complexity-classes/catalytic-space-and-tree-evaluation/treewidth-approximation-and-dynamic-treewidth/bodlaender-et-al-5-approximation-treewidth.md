# Bodlaender–Drange–Dregi–Fomin–Lokshtanov–Pilipczuk: a 2^{O(k)} n time 5-approximation for treewidth

There is an algorithm that, given an $n$-vertex graph $G$ and an integer $k > 0$, in time $2^{O(k)}\,n$ either outputs that $\operatorname{tw}(G) > k$ or outputs a tree decomposition of $G$ of width at most $5k+4$. This was the first constant-factor approximation for treewidth running in time single-exponential in $k$ and linear in $n$; before it the choices were $2^{O(k)}n^2$, $2^{O(k\log k)}n\log n$, or $k^{O(k^3)}n$.

## Proof sketch

The algorithm combines a recursive balanced-separator construction (find a small separator of the current boundary set, recurse on components) with a data structure that, given a tree decomposition of width $O(k)$ for the graph, answers separator queries in $2^{O(k)}$ time per step; a compression/contraction scheme in the style of Bodlaender's linear-time algorithm supplies that decomposition recursively from a graph with a constant fraction fewer vertices, so the total time telescopes to $2^{O(k)}n$.

## Depends on

- [FPT-approximation algorithms for treewidth](fpt-approximation-algorithms-for-treewidth.md)
- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)

## Proof depends on

- [Balanced separators of size k+1 in graphs of treewidth at most k](balanced-separators-treewidth-k.md)

## Sources

- Hans L. Bodlaender, Pål Grønås Drange, Markus S. Dregi, Fedor V. Fomin, Daniel Lokshtanov and Michał Pilipczuk, "A c^k n 5-Approximation Algorithm for Treewidth", SIAM Journal on Computing 45(2) (2016), arXiv:1304.6321.
