# Leaf counts of decision trees: depth and decision lists

Let $T$ be a binary decision tree of depth $d$. Then $T$ has at most $2^d$ leaves, its number of leaves exceeds its number of internal nodes by one, and every input follows a unique root-to-leaf path, so the answers along a path determine the leaf reached. Decision lists (trees in which every internal node has a leaf child) of depth $d$ have at most $d+1$ leaves. A tree computing a function that takes $k\ge1$ distinct values has at least $k$ leaves, hence depth at least $\log_2 k$.

## Proof sketch

Induct on the tree: a leaf has depth $0$ and one leaf, and a tree of depth $d$ has two subtrees of depth at most $d-1$. In a decision list every internal node has a leaf child, so the internal nodes form a single path of length at most $d$, carrying at most $d+1$ leaves. Each value of the function labels at least one leaf.

Derived here: if $T$ has Ehrenfeucht–Haussler rank $r$ (rank $0$ for a leaf; otherwise the maximum of the children's ranks if they differ, and one more than their common rank if equal), then $T$ has at most $\sum_{j=0}^{r} \binom{d}{j}$ leaves. A node of rank $r$ has one child of rank at most $r - 1$, whose depth is one less, and $\binom{d-1}{j} + \binom{d-1}{j-1} = \binom{d}{j}$ closes the recursion. Decision lists have rank at most $1$.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014 (Definition 3.14 and the discussion following it; Exercise 3.23 for decision lists).
