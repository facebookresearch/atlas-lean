# Quantum soundness of the low individual degree test

Let $k \ge md$. If a finite symmetric tensor strategy (swap-invariant state, identical projective measurements) passes the low individual degree test with branch losses whose $1/128$ powers sum, together with $(d/|\mathbb{F}|)^{1/128}$, to $R$, then there is a POVM $\{G_g\}$ on polynomials of individual degree at most $d$ whose mean disagreement with the point measurements is at most

$$160000\, m^2 \Big(100000\, k^2 m R + e^{-k/(80000 m^2)}\Big).$$

For general (not necessarily symmetric) projective strategies there are projective polynomial measurements on each player's original space with point and full-polynomial disagreements bounded, respectively, by $\sigma + \sqrt{8\zeta + 4\sqrt{18\zeta}}$ and $\zeta + 2\sqrt{18 \zeta}$ in the same parameters.

## Proof sketch

Induct on the dimension: restrict the strategy to slices with fixed last coordinate, apply self-improvement and the induction hypothesis on the slices, show that slice outcomes approximately commute (using diagonal lines), and paste them into polynomial outcomes on $\mathbb{F}^m$; the error recursion over $m$ steps gives the stated bound. Non-symmetric strategies are reduced to symmetric ones by symmetrization.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Self-improvement for symmetric low individual degree strategies](self-improvement-for-symmetric-strategies.md)
- [Classical soundness of the low individual degree test](classical-soundness-of-low-individual-degree-test.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
