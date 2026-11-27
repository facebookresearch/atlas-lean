# Dinur–Kaufman: high-dimensional expanders support 99%-agreement tests

Let $X$ be a $d$-dimensional two-sided $\lambda$-local spectral expander and $k \le \sqrt{d}$, and let $\mathcal{F} = X(k-1)$ with the test that samples a $(2k-1)$-face $\sigma$ of $X$ and two $(k-1)$-faces $s_1, s_2 \subset \sigma$ with $|s_1 \cap s_2| = k/2$. If $\lambda \le \lambda_0(k)$ then every ensemble with $\operatorname{Agr}(\{f_s\}) \ge 1 - \varepsilon$ is $O(\varepsilon)$-close to a global function $G : X(0) \to \Sigma$. Taking $X$ from a bounded-degree family yields an agreement test with $|\mathcal{F}| = O(|X(0)|)$, a linear-size derandomization of the direct product test in the high-acceptance regime.

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
