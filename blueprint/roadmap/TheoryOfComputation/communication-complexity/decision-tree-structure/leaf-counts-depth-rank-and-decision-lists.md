# Leaf counts of decision trees: depth, rank and decision lists

Let $T$ be a binary decision tree of depth $d$. Then $T$ has at most $2^d$ leaves, its number of leaves exceeds its number of internal nodes by one, and the answers along a root-to-leaf path determine the leaf reached. If $T$ has Ehrenfeucht–Haussler rank $r$ (rank $0$ for a leaf; otherwise the maximum of the children's ranks if they differ, and one more than their common rank if equal), then $T$ has at most $\sum_{j=0}^{r} \binom{d}{j}$ leaves. Decision lists (trees in which every internal node has a leaf child) have rank at most $1$, hence at most $d + 1$ leaves. A tree computing a function that takes $k\ge1$ distinct values has at least $k$ leaves, hence depth at least $\log_2 k$.

## Proof sketch

Induct on the tree. For the rank bound, a node of rank $r$ has one child of rank at most $r - 1$, whose depth is one less, and $\binom{d-1}{j} + \binom{d-1}{j-1} = \binom{d}{j}$ closes the recursion.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
