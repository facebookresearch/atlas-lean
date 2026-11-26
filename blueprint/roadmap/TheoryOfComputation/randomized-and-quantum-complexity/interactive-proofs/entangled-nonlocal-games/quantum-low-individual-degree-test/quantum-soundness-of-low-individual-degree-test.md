# Quantum soundness of the low individual degree test

Let $q = |\mathbb{F}|$ and let $k \ge md$ be an integer. If a symmetric strategy (swap-invariant state, identical measurements for both players) passes the axis-parallel lines test, the self-consistency test and the diagonal lines test with probabilities at least $1 - \varepsilon$, $1 - \delta$ and $1 - \gamma$, then there is a measurement $\{G_g\}$ on polynomials of individual degree at most $d$ whose mean disagreement with the point measurements is at most

$$\sigma = m^2 \cdot 1000\, k^2 m^2 \big(\varepsilon^{1/1024} + \delta^{1/1024} + \gamma^{1/1024} + (d/q)^{1/1024}\big) + e^{-k/(80000 m^2)}$$

(Ji et al. 2020, Theorem 6.1). For an arbitrary projective strategy passing the whole test with probability at least $1 - \varepsilon$, there are projective measurements $G^A, G^B$ on such polynomials that are consistent with each player's point measurements and with each other up to error $100000\, k^2 m^4 \big(\varepsilon^{1/40000} + (d/q)^{1/40000} + e^{-k/(2560000 m^2)}\big)$ (Ji et al. 2020, Theorem 3.10).

## Proof sketch

Induct on the dimension: restrict the strategy to slices with fixed last coordinate, apply self-improvement and the induction hypothesis on the slices, show that slice outcomes approximately commute (using diagonal lines), and paste them into polynomial outcomes on $\mathbb{F}^m$; the error recursion over $m$ steps gives the bound for symmetric strategies. Non-symmetric strategies are reduced to symmetric ones by symmetrization, and orthogonalization makes the measurements projective.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Self-improvement for symmetric low individual degree strategies](self-improvement-for-symmetric-strategies.md)
- [Classical soundness of the low individual degree test](classical-soundness-of-low-individual-degree-test.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
