# Connected covers obstruct low-soundness agreement on high-dimensional expanders

Let $0<\zeta<1/2$, $k\in\mathbb{N}$ and $\lambda\le 0.99/k$. Let $X$ be a $k$-dimensional $\lambda$-two-sided high-dimensional expander that has a connected $\ell$-cover $\rho:Y\to X$ for some $\ell>1$. Then for every test distribution $D$ on pairs of $k$-faces whose marginal is the face distribution there is an ensemble $\mathcal{F}=\{f_r:r\to\{0,1\}\}_{r\in X(k)}$ whose acceptance probability $\mathrm{Agree}_D(\mathcal{F})$ in the two-query agreement test with distribution $D$ is at least $1/\ell$, and yet for every global function $G:X(0)\to\{0,1\}$,

$$
\Pr_{r\in X(k)}\bigl[f_r \text{ agrees with } G|_r \text{ on at least a } (1-\zeta)\text{-fraction of } r\bigr]\ \le\ \exp(-\Omega_\zeta(k)).
$$

The bound depends on the face dimension $k$, not on the number of vertices: with fixed face size and alphabet a uniformly random $G$ matches any given face exactly with constant probability, so no vanishing bound in $|X(0)|$ is possible. Hence the low-acceptance agreement theorem fails on every such complex with a connected cover.

## Proof sketch

For $\ell=2$ (the case written out in the source), write $Y(0)=X(0)\times\{0,1\}$ with $\rho(v,i)=v$ and $H(v,i)=i$. For each face $r\in X(k)$ choose one of its two preimages $\tilde r$ independently and uniformly at random and set $f_r=H|_{\tilde r}$, read through $\rho$. For a pair $(r,r')$ drawn by the test, whose marginal on each face is the face distribution, the lifts contain the same preimage of a common vertex with probability $1/2$, and then, since $\rho$ is a local isomorphism, the same preimage of every common vertex, so $f_r$ and $f_{r'}$ agree on $r\cap r'$; hence the expected acceptance under the fixed $D$ is at least $1/2$, and some realization of the random ensemble attains it. For a global $G$, let $\tilde G(v,i)=G(v)$; if $f_r$ agrees with $G|_r$ on a $(1-\zeta)$-fraction of $r$, then $\tilde G$ agrees with $H$ on that fraction of $\tilde r$. The labellings $H$ and $\tilde G$ disagree on exactly half of $Y(0)$, and $Y$ inherits two-sided spectral expansion from $X$, so the sampling property of high-dimensional expanders bounds the fraction of $k$-faces of $Y$ meeting that set in less than a $\zeta$-fraction by $\exp(-\Omega(\zeta^2k))$.

## Depends on

- [Connected covers of a simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/covers-of-complexes.md)
- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)
- [Agreement tests for ensembles of local functions](agreement-test.md)

## Sources

- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the low acceptance regime: the role of covers", STOC (2024), arXiv:2308.09582v2, ECCC TR23-119 (Lemma 1.2 and §7.1).
- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
