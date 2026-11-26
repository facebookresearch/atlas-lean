# Korhonen–Lokshtanov: exact treewidth in time 2^{O(k^2)} n^{O(1)}

There is an algorithm that, given an $n$-vertex graph $G$ and an integer $k$, runs in time $2^{O(k^2)}\,n^{O(1)}$ and outputs a tree decomposition of $G$ of width at most $k$ if one exists (and reports that none exists otherwise). This is the first improvement in the dependence on $k$ since the $2^{O(k^3)}n^{O(1)}$ algorithms of Bodlaender–Kloks and Lagergren–Arnborg (1991), and resolves the question of whether treewidth can be computed in $2^{o(k^3)}n^{O(1)}$ time. The algorithm works in polynomial space.

## Proof sketch

The algorithm repeatedly improves a decomposition of width $k+1$ to one of width $k$ (or certifies none exists) through a local improvement operation generalizing Korhonen's split: a largest bag is refined using a "minimum split" computed by an enumeration over $2^{O(k^2)}$ candidate configurations, and a potential function based on bag sizes strictly decreases. Iterative compression handles the initial decomposition.

## Depends on

- [FPT-approximation algorithms for treewidth](fpt-approximation-algorithms-for-treewidth.md)

## Proof depends on

- [Korhonen: a single-exponential time 2-approximation for treewidth](korhonen-2-approximation-treewidth.md)

## Sources

- Tuukka Korhonen and Daniel Lokshtanov, "An Improved Parameterized Algorithm for Treewidth", STOC (2023), arXiv:2211.07154.
