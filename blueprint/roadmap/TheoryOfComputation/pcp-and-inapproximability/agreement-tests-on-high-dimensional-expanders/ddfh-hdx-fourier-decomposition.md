# Boolean function analysis on HDX: approximate eigen-decomposition of the up-down walk

Let $X$ be a $d$-dimensional two-sided $\lambda$-local spectral expander and $0 \le k \le d$. Every $f : X(k) \to \mathbb{R}$ decomposes uniquely as $f = \sum_{i=-1}^{k} U^{k-i} h_i$ where $h_i : X(i) \to \mathbb{R}$ satisfies $D_i h_i = 0$ for $i \ge 0$ (and $U^{j}$ denotes iterated up operators). The components are approximately orthogonal and approximately eigenvectors of the up-down walk:

$$
\Bigl\| N_k^{\wedge} U^{k-i}h_i - \Bigl(1 - \frac{i+1}{k+2}\Bigr) U^{k-i}h_i \Bigr\| \le O_k(\lambda)\, \|U^{k-i} h_i\|.
$$

For the complete complex this recovers the Johnson-scheme eigenspace decomposition, and for $\lambda < 1/d$ and $4k^2 < d$ it yields a Friedgut–Kalai–Naor theorem on $X(k)$: if $F : X(k) \to \{0,1\}$ satisfies $\mathbb{E}[(F - f)^2] < \varepsilon$ for some $f = U^{k+1} h_{-1} + U^{k} h_0$ of degree $1$, then $F$ agrees with a degree-$1$ function $g(s) = \sum_{v \in s} d_v$, $d_v \in \{0, 1, \tfrac{1}{k+1}, \tfrac{1}{k+1} - 1\}$, on all but an $O_\lambda(\varepsilon)$-fraction of $X(k)$.

## Proof sketch

Construct $h_i$ by inverting the up operators on the orthogonal complements of lower levels, using that $D U - U D$ is close to a scalar on each level when links are spectral expanders. The commutation relation, proved by localizing to links where the walks become $1$-skeleton walks with eigenvalues bounded by $\lambda$, gives both approximate orthogonality and the approximate eigenvalues.

## Depends on

- [Up-down and down-up random walks on a weighted complex](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/up-down-walks.md)
- [Local spectral expanders (one-sided and two-sided)](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/local-spectral-expander.md)

## Proof depends on

- [Spectral gap of high-order walks on local spectral expanders](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/kaufman-oppenheim-walk-gap.md)
- [Friedgut–Kalai–Naor (FKN) Theorem](../../../Combinatorics/boolean-functions/structure-theorems-for-boolean-functions/fkn-theorem.md)

## Sources

- Y. Dikstein, I. Dinur, Y. Filmus, P. Harsha, "Boolean function analysis on high-dimensional expanders", APPROX-RANDOM (2018); Combinatorica 44 (2024), arXiv:1804.08155.
- T. Kaufman, I. Oppenheim, "High order random walks: beyond spectral gap", APPROX-RANDOM (2018); Combinatorica 40 (2020), arXiv:1707.02799.
