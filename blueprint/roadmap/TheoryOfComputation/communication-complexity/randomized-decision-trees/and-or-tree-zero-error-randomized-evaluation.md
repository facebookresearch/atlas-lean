# Snir / Saks–Wigderson: the AND–OR tree in n^{log₄ 3} expected queries

The *directional* algorithm evaluates a NAND node by evaluating a uniformly random child first and the other child only if needed. It computes the complete binary NAND tree (equivalently the AND–OR tree) with zero error, and its expected number of queries on every input of the depth-$2k$ tree with $n = 4^k$ leaves is at most $3^k = n^{\log_4 3} \approx n^{0.793}$, whereas every deterministic algorithm needs $n$ queries.

## Proof sketch

Let $a_d$ and $b_d$ be the largest expected costs, over inputs of the NAND tree of height $d$, on which it evaluates to $1$ and to $0$; $a_0 = b_0 = 1$. A NAND node with value $0$ needs both children, each of value $1$, so $b_{d+1} = 2a_d$. A node with value $1$ has a child of value $0$: if both children are $0$ the cost is $b_d$, and otherwise the $0$-child is evaluated first with probability $1/2$, so $a_{d+1} \le \frac12 b_d + \frac12(a_d + b_d) = b_d + \frac12 a_d$. With $M_d = \max(a_d, b_d)$ this gives $b_{d+2} = 2a_{d+1} \le 2b_d + a_d \le 3M_d$ and $a_{d+2} \le b_{d+1} + \frac12 a_{d+1} \le 2a_d + \frac12\big(b_d + \frac12 a_d\big) \le 3M_d$, so $M_{2k} \le 3^k$.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)

## Proof depends on

- [The complete AND–OR tree is evasive](../decision-tree-structure/and-or-tree-is-evasive.md)

## Sources

- M. Snir, "Lower Bounds on Probabilistic Linear Decision Trees", Theoretical Computer Science 38, 1985.
- M. Saks and A. Wigderson, "Probabilistic Boolean Decision Trees and the Complexity of Evaluating Game Trees", FOCS 1986.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
