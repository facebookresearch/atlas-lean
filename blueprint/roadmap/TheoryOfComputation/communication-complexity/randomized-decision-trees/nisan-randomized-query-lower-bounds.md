# Nisan: block sensitivity and approximate degree lower-bound randomized query complexity

For every Boolean function $f$ and $0 \le \varepsilon < 1/2$: $(1 - 2\varepsilon)\, bs(f) \le R_\varepsilon(f)$, and in fact every randomized decision tree computing $f$ with error $\varepsilon$ has, on some input, an expected number of executed queries at least $(1 - 2\varepsilon)\, bs(f)$; moreover $\widetilde{\deg}_\varepsilon(f) \le R_\varepsilon(f)$. Consequently $D(f) \le \deg(f)\, bs(f) = O(R_{1/3}(f)^3)$, so deterministic and bounded-error randomized query complexity are polynomially related.

## Proof sketch

Let $x$ have disjoint sensitive blocks $B_1, \dots, B_b$. A tree that queries no variable of $B_j$ on input $x$ reaches the same leaf on $x$ and on $x^{B_j}$ and errs on one of them; disjointness bounds by the expected number of queries the number of blocks touched, and averaging the errors gives the bound. The acceptance probability of a depth-$q$ randomized tree is a polynomial of degree at most $q$.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)
- [Approximate degree of a Boolean function](../sensitivity-certificates-and-degree/approximate-degree-of-a-boolean-function.md)

## Proof depends on

- [Midrijanis: D(f) ≤ deg(f)·bs(f) ≤ 2 deg(f)³](../sensitivity-certificates-and-degree/midrijanis-degree-bound.md)

## Sources

- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
