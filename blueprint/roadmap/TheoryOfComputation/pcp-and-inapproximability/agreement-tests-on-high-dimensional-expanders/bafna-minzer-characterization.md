# Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing

Let $X$ be a $d$-dimensional $\lambda$-local spectral expander with $\lambda$ sufficiently small and $d$ sufficiently large. Bafna and Minzer (Theorem 1.9; necessity in Theorem 3.1, sufficiency in Theorem 4.1 and Remark 4.2) give a qualitative characterization of low-soundness direct product testing on $X(k)$ in terms of **weak unique-games coboundary expansion** of the graphs $G_t[X]$ on $t$-faces:

1. **Sufficiency (Theorem 4.1):** If the graphs $G_t[X]$ for all $t \le r$ (with $r = \exp(\operatorname{poly}(1/\delta))$, $\xi = \operatorname{poly}(\delta)$, and $d > \operatorname{poly}(k)\exp(1/\delta)$) satisfy weak unique-games coboundary expansion over $S_m$ (for $(1-\xi)$-strongly triangle-consistent instances), then the $2$-query direct product test on $X(k)$ is sound at acceptance $\delta$: every $F : X(k) \to \{0,1\}^k$ passing with probability at least $\delta$ agrees with a global direct product function on a $\operatorname{poly}(\delta)$-fraction of faces up to small error.
2. **Necessity (Theorem 3.1):** Conversely, if some $G_t[X]$ fails weak unique-games coboundary expansion over $S_m$ with parameter $\xi$, then there is an ensemble passing the direct product test with probability at least $1/m - O(\sqrt{\xi})$ that is far from every direct product function (ordinary non-weak UG coboundary expansion of links is not claimed to be necessary, and the two directions are not equivalent up to polynomial parameter losses).

Independently, Dikstein and Dinur (STOC 2024, Lemma 1.2 and Theorem 1.3) characterize low-soundness agreement testing on high-dimensional expanders through absence of connected covers together with swap-cosystolic expansion.

## Proof sketch

For sufficiency, a passing ensemble induces on the $t$-face graphs $G_t[X]$ a partial matching of local list-decoding candidates that forms a $(1-\xi)$-strongly triangle-consistent $S_m$-valued $1$-cochain; weak UG coboundary expansion trivializes it, gluing local candidates into a global direct product function. Conversely, a strongly triangle-consistent $S_m$-cochain on $G_t[X]$ with no approximate global trivialization induces a cover-like ensemble passing the test with probability $1/m - O(\sqrt{\xi})$ while remaining far from any direct product.

## Depends on

- [Non-abelian 1-cochains and unique-games coboundary expansion](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/nonabelian-cochain.md)

## Proof depends on

- [Connected covers obstruct low-soundness agreement on high-dimensional expanders](covers-obstruct-low-soundness.md)

## Sources

- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668 (Definitions 1.4, 1.7, 1.8, Theorems 1.9, 3.1, 4.1, Remark 4.2).
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", STOC (2024), arXiv:2308.09582, ECCC TR23-119 (Lemma 1.2, Theorem 1.3).
