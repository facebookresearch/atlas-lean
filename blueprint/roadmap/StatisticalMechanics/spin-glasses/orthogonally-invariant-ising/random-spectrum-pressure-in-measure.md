# Invariant Ising pressure convergence in measure for random spectra

Let the eigenvalue vector $\lambda_N$ and real pressure $Y_N$ be measurable on a probability space. At each $N$ suppose the joint law of $(\lambda_N,Y_N)$ equals the law of $(\lambda_N,P_N(0))$ obtained by drawing $\lambda_N$ with its marginal law and an independent right Haar rotation on $O(N)$ in the [finite-pressure model](rotated-spin-pressure.md). Suppose the empirical spectral laws converge in probability in the Lévy–Prokhorov metric to a compactly supported probability $\nu$ with support contained in $[a,b]$ and containing $a,b$. Also suppose $\max(0,\max_i(a-\lambda_{Ni}),\max_i(\lambda_{Ni}-b))\to0$ in probability. Then $Y_N$ converges in measure to the real projection of $V(\nu,b)$.

**Conventions.** Use the joint-law conditional Haar condition, the empirical spectral measure at positive sizes, the scalar spectral excess and the Lévy–Prokhorov topology on probabilities.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

- [Deterministic spectral pressure under no outliers](positive-temperature-pressure.md)

## Expansion

Take subsequences with almost-sure spectral convergence and excess control, then transfer bounded disorder-error probabilities through the joint-law identity. Do not infer an almost-sure conclusion from convergence of the spectral data in probability alone.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L357-L376)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
- [Pinned model and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L208-L280)
