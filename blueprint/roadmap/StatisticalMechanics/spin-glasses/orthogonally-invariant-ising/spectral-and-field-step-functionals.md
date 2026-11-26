# Spectral and magnetic field-step functionals

Define $G(z)=\int (z-y)^{-1}\,d\nu(y)$; for $x>0$ put $R(x)=z-1/x$ if $G(z)=x$ has a solution $z>b$, and $R(x)=b-1/x$ if it has none. For $x\le0$ put $R(x)=\int y\,d\nu(y)$. For every nondecreasing $p:\mathbb R\to[0,1]$, let $d_p(r)=1-r-\int_0^1(p(u)-r)_+\,du$. Use all ordered field-step tests with cuts $0=s_0<\cdots<s_m=1$, heights $0\le h_0\le\cdots\le h_{m-1}$, and $h(u)=h_i$ on open cells (zero at cuts). Let $L_h(z)$ be the Gaussian recursion applied to $\log\cosh$ starting at $z$, minus $h_{m-1}/2$: compose transformations from outermost $i=0$ to innermost $i=m-1$, with variance $h_i-h_{i-1}$ ($h_{-1}=0$) and logarithmic power-mean exponent $s_i$; at exponent zero use ordinary Gaussian expectation. The zero-field variational functional is

$$
V(\nu,b)=\inf_p\left[\sup_h\left(L_h(0)+\tfrac12\int_0^1 h(u)p(u)\,du\right)+\tfrac12\int_0^1 R(d_p(r))\,dr\right].
$$

The trial suprema and infima are extended real. Use totalized real projection (either infinity projects to zero) and the usual totalized Bochner integrals (zero on nonintegrable functions).

For a simple field with positive masses $\gamma_a$ at heights $c_a$ (discard null atoms), replace the zero-field entropy test term $L_h(0)$ by $\sum_a\gamma_a\inf_{z\in\mathbb R}(L_h(z)-zs_a)$. For fixed group magnetizations $s_a\in\mathbb Q\cap(-1,1)$ use the same field-step supremum and overlap infimum and the same spectral term as before. Add $\sum_a\gamma_ac_as_a$ and take the extended-real supremum over these rational magnetizations. For general $\xi$, write $s_j$ for the $j$th `SimpleFunc.approxOn` approximant to the real identity, with target set $\operatorname{range}(\mathrm{id})\cup\{0\}$ and default $0$. For each $j$, take the real projection of the extended simple-field value with heights in the finite range of $s_j$ and masses $\xi\{x:s_j(x)=c_a\}$, retaining positive masses only. The functional is `limUnder atTop` of that real sequence, with its native totalization; this definition does not assume either convergence of these scalar values or $L^1$ convergence of the approximants.

## Depends on

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L61-L196)
