# Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing

Consider the **$(k, \sqrt{k})$ direct product test** (Bafna–Minzer, Agreement-Test 1 with $s = \sqrt{k}$) on a $d$-dimensional simplicial complex $X$: sample a $d$-face $D$, an $s$-subset $I \subseteq D$, and two $k$-faces $A, B \subseteq D$ containing $I$, and accept if $F[A]|_I = F[B]|_I$. Bafna and Minzer (Theorem 1.9; necessity in Theorem 3.1, sufficiency in Theorem 4.1 and Remark 4.2) give a qualitative characterization of low-soundness direct product testing on spectral high-dimensional expanders in terms of **weak $(m, r, \xi, c)$ unique-games (UG) coboundary expansion** of the $t$-face graphs $G_t[X]$ ($t \le r$):

1. **Sufficiency (Theorem 4.1 and Remark 4.2):** There is an absolute constant $c > 0$ such that for all $\varepsilon, \delta > 0$ there exist $\xi, \eta > 0$ and $m, r \in \mathbb{N}$ (specifically $r = \exp(\operatorname{poly}(1/\delta))$ and $\xi = \operatorname{poly}(\delta)$) such that for all sufficiently large $k$ (with $\delta \ge 1/\log k$), all sufficiently large $d$ (with $d \ge \operatorname{poly}(k)\exp(1/\delta)$), and $\gamma > 0$ sufficiently small as a function of $d$: if a $d$-dimensional complex $X$ is a $\gamma$-spectral expander and a weak $(m, r, \xi, c)$ UG coboundary expander, then every $F \colon X(k) \to \{0,1\}^k$ passing the $(k, \sqrt{k})$ test with probability at least $\delta$ satisfies $\Pr_{A \sim \mu_k}[\Delta(F[A], f|_A) \le \varepsilon] \ge \eta$ for some global function $f \colon X(1) \to \{0,1\}$.
2. **Necessity (Theorem 3.1):** Conversely, for all $c, \eta > 0$ and $m, r \in \mathbb{N}$ there exist $d, k \in \mathbb{N}$ and $\xi, \gamma > 0$ such that if a $d$-dimensional $\gamma$-spectral expander $X$ is not a weak $(m, r, \xi, c)$ UG coboundary expander, then there exists $F \colon X(k) \to \{0,1\}^k$ passing the $(k, \sqrt{k})$ test with probability at least $1/m - O(\sqrt{\xi})$ such that every global function $f \colon X(1) \to \{0,1\}$ agrees with $F$ up to Hamming distance $\Omega_{m,r,c}(1)$ on at most an $\eta$-fraction of $k$-faces (ordinary non-weak UG coboundary expansion is not claimed to be necessary, and the two directions are not equivalent up to polynomial parameter losses).

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
