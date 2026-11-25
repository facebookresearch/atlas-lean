# The four-dimensional Smale conjecture is false (Watanabe)

Write $S^4$ for the unit sphere
of $\mathbb{R}^5$ and let the orthogonal group $O(5)$ act linearly on it. There are an $n \ge 1$,
a compact, Hausdorff, second-countable smooth manifold $X$ with boundary modelled on the
$n$-dimensional half-space, with boundary $\partial X$, smooth maps
$F, F' : X \times S^4 \to S^4$ with $F(x, F'(x, p)) = p$ and $F'(x, F(x, p)) = p$ for all
$x \in X$ and $p \in S^4$, and a continuous map $\psi_\partial : \partial X \to O(5)$ with
$F(b, p) = \psi_\partial(b)\, p$ for all $b \in \partial X$ and $p \in S^4$, such that the
following fails: there are a continuous map $\psi : X \to O(5)$ that agrees with
$\psi_\partial$ on $\partial X$ and smooth maps $H, H' : X \times [0, 1] \times S^4 \to S^4$
such that for all $x \in X$, $t \in [0, 1]$ and $p \in S^4$ we have
$H(x, t, H'(x, t, p)) = p$, $H'(x, t, H(x, t, p)) = p$, $H(x, 0, p) = F(x, p)$ and
$H(x, 1, p) = \psi(x)\, p$, and $H(b, t, p) = F(b, p)$ whenever $b \in \partial X$.

In other words, the relative parametrized form of the statement that $O(5) \to \mathrm{Diff}(S^4)$
is a homotopy equivalence, the analogue of Hatcher's theorem for $S^3$, does not hold.

## Sources

- T. Watanabe, *Some exotic nontrivial elements of the rational homotopy groups of Diff(S⁴)*, arXiv:1812.02448 (2018). Pairs with the positive S³ statement of Hatcher (Ann. of Math. 117, 1983). Problem `watanabe_four_dim_smale_disproof` of the lean-eval benchmark.
