# Bafna–Lifshitz–Minzer: constant-degree direct product testers with small soundness

For every $\delta, \varepsilon > 0$ there are $\eta = \eta(\delta, \varepsilon) > 0$, an integer $k$ (which may be taken arbitrarily large) and an infinite family of high-dimensional expanders $\{X_n\}$ with all vertex degrees bounded by a constant depending only on $\delta$ and $\varepsilon$ such that the $2$-query $(k, \sqrt{k})$ direct product tester on $X_n(k)$ has soundness $\delta$ in the following sense: every $F : X_n(k) \to \{0,1\}^k$ with $\Pr[\text{test accepts}] \ge \delta$ has a global function $f : X_n(1) \to \{0,1\}$ with $\Pr_{A}[\Delta(F[A], f|_A) \le \varepsilon k] \ge \eta$, i.e. $F$ agrees with the direct product function $(f(\sigma_1), \dots, f(\sigma_k))$ up to an $\varepsilon$-fraction of coordinates on at least an $\eta$-fraction of $k$-faces. This resolves the Dinur–Kaufman conjecture that bounded-degree complexes admit direct product tests in the small soundness regime.

## Proof sketch

By Bafna and Minzer's improved sufficiency direction on the characterization page (Theorem B.1; BLM Theorem 1.8) it suffices to show that suitable Chapman–Lubotzky complexes are $\gamma$-spectral expanders and $(m, r, 2^{-r/\log\log\log r}, c)$ UG coboundary expanders of their face graphs $G_t[X]$, $t \le r$; Bafna, Lifshitz and Minzer prove the stronger (non-weak) UG coboundary expansion of these graphs (Theorem 6.12, applied through their Theorem 1.8), from cosystolic expansion of $G_r[X]$, obtained from coboundary expansion of its vertex links, together with vanishing $1$-cohomology over $S_m$ (a function that is strongly triangle consistent is triangle consistent, so the non-weak notion implies the weak one). The main technical contribution is a general technique showing coboundary expansion of non-abelian coefficient cochains on the links via a decomposition of link cycles into short cycles that are themselves contractible through cones with bounded overlap, combined with local spectral expansion for the global step.

## Depends on

- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)

## Proof depends on

- [Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing](bafna-minzer-characterization.md)

## Sources

- M. Bafna, N. Lifshitz, D. Minzer, "Constant degree direct product testers with small soundness", FOCS (2024), arXiv:2402.00850 (Theorem 1.3, Definition 1.7, Theorem 1.8, Theorem 6.12 and Section 6.4).
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668 (Theorem B.1).
