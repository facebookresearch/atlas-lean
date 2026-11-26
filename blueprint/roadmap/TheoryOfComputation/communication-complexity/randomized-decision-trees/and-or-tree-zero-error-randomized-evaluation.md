# Snir / Saks–Wigderson: the AND–OR tree in n^{log₄ 3} expected queries

The *directional* algorithm evaluates a NAND node by evaluating a uniformly random child first and the other child only if needed. It computes the complete binary NAND tree (equivalently the AND–OR tree) with zero error, and its expected number of queries on every input of the depth-$2k$ tree with $n = 4^k$ leaves is at most $3^k = n^{\log_4 3} \approx n^{0.793}$, whereas every deterministic algorithm needs $n$ queries.

## Proof sketch

Let $a_d$ and $b_d$ bound the expected cost on inputs evaluating to $1$ and to $0$ at depth $d$. A NAND node with value $0$ needs both children (each of value $1$), and one with value $1$ has a child of value $0$ found first with probability at least $1/2$. The recurrences $b_{d+1} = 2 a_d$, $a_{d+1} \le b_d + \frac12 a_d$ (and symmetric variants) solve to growth $3$ per two levels.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)

## Proof depends on

- [The complete AND–OR tree is evasive](../decision-tree-structure/and-or-tree-is-evasive.md)

## Sources

- M. Snir, "Lower Bounds on Probabilistic Linear Decision Trees", Theoretical Computer Science 38, 1985.
- M. Saks and A. Wigderson, "Probabilistic Boolean Decision Trees and the Complexity of Evaluating Game Trees", FOCS 1986.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
