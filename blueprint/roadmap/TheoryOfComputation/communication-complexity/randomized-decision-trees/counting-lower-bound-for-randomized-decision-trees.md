# Counting lower bound for randomized decision trees

Let $F$ be injective on a finite set $S$ of inputs and let a randomized decision tree of depth at most $q$ output $F(x)$ with error at most $\varepsilon$ on every $x \in S$. Then $|S|(1 - \varepsilon) \le 2^q$.

## Proof sketch

Each supported tree has at most $2^q$ leaves, so it is correct on at most $2^q$ inputs of $S$; averaged over the trees, at least $|S|(1-\varepsilon)$ correct answers occur.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)

## Proof depends on

- [Leaf counts of decision trees: depth and decision lists](../decision-tree-structure/leaf-counts-depth-rank-and-decision-lists.md)

## Sources

- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
