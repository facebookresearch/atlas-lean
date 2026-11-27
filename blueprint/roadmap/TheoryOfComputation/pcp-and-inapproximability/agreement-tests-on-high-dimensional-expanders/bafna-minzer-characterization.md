# Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing

Let $X$ be a $d$-dimensional $\lambda$-local spectral expander with $\lambda$ sufficiently small in terms of $\delta > 0$ and $d$ sufficiently large in terms of $\delta$. Then the following are equivalent up to polynomial losses in the parameters.

1. The $2$-query direct product test on $X(k)$ is sound with soundness $\delta$: every $F : X(k) \to \{0,1\}^k$ that passes with probability at least $\delta$ is $\operatorname{poly}(\delta)$-correlated with a direct product function on a $\operatorname{poly}(\delta)$-fraction of faces.
2. Links of $X$ (and of suitable faces) satisfy unique-games coboundary expansion with coefficients $S_m$, $m \le \operatorname{poly}(1/\delta)$, with expansion constant depending only on $\delta$.

## Proof sketch

For the direction from coboundary expansion to soundness, a successful ensemble induces on each link a partial matching of local list-decoding candidates, that is, an $S_m$-valued $1$-cochain whose triangle holonomies are mostly trivial; coboundary expansion trivializes the cochain, which glues local candidates into a global direct product function. Conversely, a nontrivial almost-cocycle produces a cover-like ensemble that passes the test while being far from any direct product.

## Depends on

- [Non-abelian 1-cochains and unique-games coboundary expansion](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/nonabelian-cochain.md)

## Proof depends on

- [Connected covers obstruct low-soundness agreement on high-dimensional expanders](covers-obstruct-low-soundness.md)

## Sources

- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
