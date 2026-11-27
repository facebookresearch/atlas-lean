# Nisan: block sensitivity and approximate degree lower-bound randomized query complexity

For every Boolean function $f$ and $0 \le \varepsilon < 1/2$, every randomized decision tree computing $f$ with error $\varepsilon$ has, on some input, an expected number of executed queries at least $(1 - 2\varepsilon)\, bs(f)$; in particular $bs(f) \le R_0(f)$ for the expected-cost zero-error complexity, and $(1 - 2\varepsilon)\, bs(f) \le R_\varepsilon(f)$ for $0 < \varepsilon < 1/2$. Moreover $\widetilde{\deg}_\varepsilon(f) \le R_\varepsilon(f)$ for $0 < \varepsilon < 1/2$ (and $\deg(f) \le D(f)$ at $\varepsilon = 0$, where bounded-depth zero error is $D$). Consequently, with $D(f)\le bs(f)^3$, $D(f) = O(R_{1/3}(f)^3)$ (Nisan), so deterministic and bounded-error randomized query complexity are polynomially related.

## Proof sketch

Let $x$ have disjoint sensitive blocks $B_1, \dots, B_b$. Let $q_j$ be the probability that the drawn tree queries a variable of $B_j$ on input $x$. A tree that does not reaches the same leaf on $x$ and on $x^{B_j}$ and is correct on at most one of them, so $2(1-\varepsilon) \le 1 + q_j$, i.e. $q_j \ge 1 - 2\varepsilon$; by disjointness of the blocks the expected number of queries on $x$ is at least $\sum_j q_j \ge (1-2\varepsilon)\,b$. The acceptance probability of a depth-$q$ randomized tree is a polynomial of degree at most $q$.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)
- [Approximate degree of a Boolean function](../sensitivity-certificates-and-degree/approximate-degree-of-a-boolean-function.md)

## Proof depends on

- [Decision-tree depth is at most certificate complexity times block sensitivity](../sensitivity-certificates-and-degree/decision-tree-depth-certificate-block-sensitivity.md)

## Sources

- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
