# Bafna–Lifshitz–Minzer: constant-degree direct product testers with small soundness

For every $\delta > 0$ there is an infinite family of high-dimensional expanders $\{X_n\}$ with all vertex degrees bounded by $O_\delta(1)$ such that the $2$-query direct product tester on $X_n(k)$ for a suitable $k = k(\delta)$ has soundness $\delta$: every $F : X_n(k) \to \{0,1\}^k$ with $\Pr[\text{test accepts}] \ge \delta$ agrees with some direct product function $(f(\sigma_1), \dots, f(\sigma_k))$ on at least a $\operatorname{poly}(\delta)$-fraction of faces, up to a small fraction of coordinates. This resolves the Dinur–Kaufman conjecture that bounded-degree complexes admit direct product tests in the small soundness regime.

## Proof sketch

By the characterization theorem it suffices to establish unique-games coboundary expansion for the relevant links of suitable Chapman–Lubotzky type complexes. The main technical contribution is a general technique showing coboundary expansion of non-abelian coefficient cochains on the links via a decomposition of link cycles into short cycles that are themselves contractible through cones with bounded overlap, combined with local spectral expansion for the global step.

## Depends on

- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)

## Proof depends on

- [Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing](bafna-minzer-characterization.md)

## Sources

- M. Bafna, N. Lifshitz, D. Minzer, "Constant degree direct product testers with small soundness", FOCS (2024), arXiv:2402.00850.
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
