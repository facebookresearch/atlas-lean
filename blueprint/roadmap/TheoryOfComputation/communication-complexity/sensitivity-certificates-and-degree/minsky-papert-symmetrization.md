# Minsky–Papert symmetrization

Let $p : \{0,1\}^n \to \mathbb{R}$ be a multilinear polynomial of degree at most $d$. Its *layer average* $P(k) = \binom{n}{k}^{-1} \sum_{|x| = k} p(x)$, for $k = 0, \dots, n$, agrees with a univariate real polynomial of degree at most $d$. In particular, if $p$ approximates a symmetric function, the univariate polynomial approximates its weight profile with the same error.

## Proof sketch

By linearity it suffices to treat a monomial $\prod_{i \in S} x_i$ with $|S| \le d$; its average over inputs of weight $k$ is $\binom{k}{|S|}/\binom{n}{|S|}$, a polynomial in $k$ of degree $|S|$.

## Depends on

- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Sources

- M. Minsky and S. Papert, "Perceptrons: An Introduction to Computational Geometry", MIT Press, 1969.
- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
