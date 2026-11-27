# Orthogonally invariant Ising pressure with converging spectral extremes

On a probability space take measurable right Haar orthogonal matrices $U_N\in O(N)$ (no independence across sizes is assumed). For deterministic eigenvalues $\lambda_{Ni}$ at size $N$, set $H_N(\sigma)=\tfrac12\sum_i\lambda_{Ni}[(U_N^{-1}\sigma)_i]^2$ and $P_N(c)=N^{-1}\log[2^{-N}\sum_{\sigma\in\{-1,1\}^N}e^{H_N(\sigma)+\sum_i c_i\sigma_i}]$. Suppose the empirical spectral laws converge weakly to a probability $\nu$ with compact support contained in $[a,b]$, with both $a,b$ in the support, and the smallest and largest eigenvalues tend to $a,b$ respectively.

Define $G(z)=\int (z-y)^{-1}\,d\nu(y)$; for $x>0$ put $R(x)=z-1/x$ if $G(z)=x$ has a solution $z>b$, and $R(x)=b-1/x$ if it has none. For $x\le0$ put $R(x)=\int y\,d\nu(y)$. For every nondecreasing $p:\mathbb R\to[0,1]$, let $d_p(r)=1-r-\int_0^1(p(u)-r)_+\,du$. Use all ordered field-step tests with cuts $0=s_0<\cdots<s_m=1$, heights $0\le h_0\le\cdots\le h_{m-1}$, and $h(u)=h_i$ on open cells (zero at cuts). Let $L_h(z)$ be the Gaussian recursion applied to $\log\cosh$ starting at $z$, minus $h_{m-1}/2$: compose transformations from outermost $i=0$ to innermost $i=m-1$, with variance $h_i-h_{i-1}$ ($h_{-1}=0$) and logarithmic power-mean exponent $s_i$; at exponent zero use ordinary Gaussian expectation. The zero-field variational functional is

$$
V(\nu,b)=\inf_p\left[\sup_h\left(L_h(0)+\tfrac12\int_0^1 h(u)p(u)\,du\right)+\tfrac12\int_0^1 R(d_p(r))\,dr\right].
$$

The suprema and infima over field and overlap trials are in the extended reals, with the pressure conclusion taking the real projection, which sends either infinity to zero. Bochner integrals are totalized to zero when nonintegrable. Both $\mathbb E P_N(0)$ and $P_N(0)$ almost surely tend to $V(\nu,b)$ with that projection.

**Conventions.** Use Haar orthogonal disorder, the normalized-spin finite pressure, the saturated inverse of the one-sided spectral transform, and the full monotone trial/hierarchy model above.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

The all-temperature deterministic spectral-pressure comparison and concentration of Haar rotation pressure strong enough for almost-sure convergence without a coupling assumption across sizes.

## Expansion

Prove the spectral transform bridge, including its saturated branch at $b$, and retain the normalization by the uniform spin measure. Separate the variational comparison from concentration and the limits under weak convergence and spectral-extreme control.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L282-L299)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
