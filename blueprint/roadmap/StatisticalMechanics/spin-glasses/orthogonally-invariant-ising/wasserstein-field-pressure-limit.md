# Invariant Ising pressure with a limiting Wasserstein field law

Under the [deterministic spectral-extreme and Haar hypotheses](zero-field-pressure-limit.md), also take deterministic fields $c_N$ whose empirical laws converge in Wasserstein one to a probability $\xi$ with finite absolute first moment. Wasserstein one is the infimum of $\mathbb E|X-Y|$ over couplings of the laws. Then both $\mathbb E P_N(c_N)$ and $P_N(c_N)$ almost surely converge to the following magnetic functional $V_{\rm mag}(\nu,b,\xi)$.

For a simple field with positive masses $\gamma_a$ at heights $c_a$ (discard null atoms), replace the zero-field entropy test term $L_h(0)$ by $\sum_a\gamma_a\inf_{z\in\mathbb R}(L_h(z)-zs_a)$. For fixed group magnetizations $s_a\in\mathbb Q\cap(-1,1)$ use the same field-step supremum and overlap infimum and the same spectral term as before. Add $\sum_a\gamma_ac_as_a$ and take the extended-real supremum over these rational magnetizations. For general $\xi$, write $s_j$ for the $j$th `SimpleFunc.approxOn` approximant to the real identity, with target set $\operatorname{range}(\mathrm{id})\cup\{0\}$ and default $0$. For each $j$, take the real projection of the extended simple-field value with heights in the finite range of $s_j$ and masses $\xi\{x:s_j(x)=c_a\}$, retaining positive masses only. The functional is `limUnder atTop` of that real sequence, with the native totalization to an unspecified value if there is no limit; this definition does not assume either convergence of these scalar values or $L^1$ convergence of the approximants.

**Conventions.** The magnetic construction adds constrained group magnetizations, finite positive-mass field partitions and the Wasserstein metric.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)
- [The orthogonally invariant Ising pressure and field-step functional](zero-field-pressure-limit.md)

## Proof depends on

The finite-valued field variational bound with group constraints and Wasserstein-stable passage to integrable field laws.

## Expansion

Validate the groupwise bias infimum and the rational-magnetization supremum, then show the pressure estimate is Lipschitz under changing empirical fields with an optimally paired matching. Use this to control the simple-function limit; weak convergence without first-moment control does not replace Wasserstein one.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L300-L321)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
