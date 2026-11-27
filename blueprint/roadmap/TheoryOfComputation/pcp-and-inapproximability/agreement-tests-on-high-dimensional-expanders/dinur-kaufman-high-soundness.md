# Dinur–Kaufman: high-dimensional expanders support 99%-agreement tests

Let $X$ be a $d$-dimensional two-sided $\lambda$-local spectral expander with $k^2 < d$ and $\lambda < 1/d$ (or $\lambda \le \lambda_0(k)$ by passing to the $(k^2+1)$-skeleton), and consider the agreement test $D_{k,2k}$ on $k$-faces of $X$ that samples a random $2k$-face $r$ of $X$ and then chooses two $k$-faces $s_1, s_2 \subset r$ **independently** (so $|s_1 \cap s_2|$ is random rather than fixed) and checks agreement of $f_{s_1}$ and $f_{s_2}$ on $s_1 \cap s_2$. Then there is an absolute constant $C > 0$ such that every ensemble $\{f_s\}$ (over a binary alphabet, and general alphabets by repetition) with agreement probability at least $1 - \varepsilon$ satisfies $\Pr_s[f_s \equiv G|_s] \ge 1 - C\varepsilon$ for a global function $G : X(0) \to \Sigma$ (Dinur–Kaufman, Theorem 5.1). Taking $X$ from a bounded-degree family yields an agreement test with $O(|X(0)|)$ faces, a linear-size derandomization of the direct product test in the high-acceptance regime.

## Proof sketch

Define $G(v)$ by majority over $f_s(v)$ for $s \ni v$. The test's local view at each vertex link is itself an agreement test on a smaller complex; spectral expansion of high-order walks shows that disagreement with $G$ propagates from links to the global structure only with constant loss, via an averaging argument over the up-down walk with gap $\Omega(1/k)$.

## Depends on

- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)
- [Agreement tests for ensembles of local functions](agreement-test.md)
- [Local spectral expanders (one-sided and two-sided)](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/local-spectral-expander.md)

## Proof depends on

- [Spectral gap of high-order walks on local spectral expanders](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/kaufman-oppenheim-walk-gap.md)

## Sources

- I. Dinur, T. Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017), ECCC TR17-089.
- I. Dinur, Y. Filmus, P. Harsha, "Agreement tests on graphs and hypergraphs", ECCC TR17-181 (2017).
