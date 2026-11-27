# Korhonen: a single-exponential time 2-approximation for treewidth

There is an algorithm that, given an $n$-vertex graph $G$ and an integer $k$, in time $2^{O(k)}\,n$ either outputs a tree decomposition of $G$ of width at most $2k+1$ or determines that $\operatorname{tw}(G) > k$. This improves the approximation ratio of $2^{O(k)}n$-time algorithms from 5 (Bodlaender et al.) to 2.

## Proof sketch

Instead of building a decomposition top-down from separators, Korhonen improves a given decomposition locally: starting from a decomposition of width $O(k)$, a largest bag $W$ is split using a minimum-size balanced "split" of $W$ (a partition of $V$ into parts with a small separator, computed by flows), and the decomposition is rebuilt around it so that the number of bags of maximum size strictly decreases while width stays at most $2k+1$. Amortization over the decomposition, together with the standard compression framework that reduces the graph size by a constant factor per recursion level, yields $2^{O(k)}n$ total time; failure to find a split certifies $\operatorname{tw}(G) > k$ via a set without balanced separators.

## Depends on

- [FPT-approximation algorithms for treewidth](fpt-approximation-algorithms-for-treewidth.md)
- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)

## Proof depends on

- [Balanced separators of size k+1 in graphs of treewidth at most k](balanced-separators-treewidth-k.md)
- [Bodlaender–Drange–Dregi–Fomin–Lokshtanov–Pilipczuk: a 2^{O(k)} n time 5-approximation for treewidth](bodlaender-et-al-5-approximation-treewidth.md)

## Sources

- Tuukka Korhonen, "A Single-Exponential Time 2-Approximation Algorithm for Treewidth", FOCS (2021), arXiv:2104.07463.
