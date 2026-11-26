# Göös–Lovett–Meka–Watson–Zuckerman: rectangles are nonnegative juntas

Let $g = \mathrm{IND}_m$ (or the inner-product gadget on $b = \Theta(\log n)$ bits) with $m = n^{C}$ for a suitable constant $C$, and let $R \subseteq \mathcal{X}^n \times \mathcal{Y}^n$ be a combinatorial rectangle with $|R| \ge 2^{-k}|\mathcal{X}^n \times \mathcal{Y}^n|$. Then the function $z \mapsto \Pr_{(x,y) \sim R}\bigl[g^n(x,y) = z\bigr] \cdot 2^{n}$ is, up to multiplicative error $1 \pm o(1)$ and a small additive error, a conical junta of degree $O(k / \log m)$. Consequently every randomized protocol for $f \circ g^n$ of cost $k$ yields a conical junta of degree $O(k/\log m)$ approximating $f$.

## Proof sketch

Decompose $R$ into a disjoint union of subrectangles in which the conditional distribution of $x$ is blockwise dense on all but a set $I$ of fixed coordinates with $|I| = O(k/\log m)$. On each such piece the distribution of $g^n(x, y)$ restricted to the coordinates outside $I$ is close to uniform by a uniform-marginals argument, so the piece contributes approximately a conjunction on the fixed coordinates $I$.

## Depends on

- [Conical juntas and their degree](conical-junta.md)
- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)

## Proof depends on

- [Conical juntas and their degree](conical-junta.md)
- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)

## Sources

- M. Göös, S. Lovett, R. Meka, T. Watson, D. Zuckerman, "Rectangles are nonnegative juntas", STOC (2015); SIAM Journal on Computing 45 (2016) 1835-1869.
