# Korhonen: dynamic treewidth in logarithmic amortized time with width 9k+8

For every fixed $k$ there is a dynamic treewidth data structure that maintains a tree decomposition of width at most $9k+8$ of a dynamic $n$-vertex graph of treewidth at most $k$ under edge insertions and deletions, with amortized update time

$$
2^{O(k)}\log n.
$$

The data structure also maintains any dynamic programming scheme on the decomposition; in particular it gives a dynamic Courcelle theorem for CMSO$_2$ with $O_k(\log n)$ amortized update time. This improves the $2^{k^{O(1)}}n^{o(1)}$ amortized update time of Korhonen, Majewski, Nadara, Pilipczuk and Sokołowski.

## Proof sketch

The key idea is to maintain a decomposition that is "downwards well-linked": each node's adhesion can be routed into its subtree by many disjoint paths. This property allows local rotations analogous to those of splay trees, and a potential-function analysis in the style of splay trees bounds the amortized number of rotations per update by $O(\log n)$, each costing $2^{O(k)}$.

## Depends on

- [Dynamic treewidth data structures under a treewidth promise](dynamic-treewidth-data-structures.md)
- [Dynamic Courcelle's theorem: maintaining any fixed CMSO2 property on graphs of bounded treewidth](dynamic-courcelle-theorem-cmso2.md)

## Proof depends on

- [Korhonen–Majewski–Nadara–Pilipczuk–Sokołowski: dynamic treewidth with width 6k+5 and subpolynomial amortized update time](kmnps-dynamic-treewidth.md)

## Sources

- Tuukka Korhonen, "Dynamic Treewidth in Logarithmic Time", arXiv preprint (2025), arXiv:2504.02790.
