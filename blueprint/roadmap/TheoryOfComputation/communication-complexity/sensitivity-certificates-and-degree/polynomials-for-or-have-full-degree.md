# Polynomials agreeing with OR on the cube have full degree

Let $n \ge 1$, let $R$ be a nontrivial commutative ring and $p \in R[x_1, \dots, x_n]$ any polynomial (multilinear or not) with $p(x) = \mathrm{OR}(x)$ for every $x \in \{0,1\}^n$. Then $\deg p \ge n$, and $1 - \prod_{i=1}^n (1 - x_i)$ attains degree $n$. In particular over $\mathbb{F}_q$ with $q$ prime, OR has exact degree $n$.

## Proof sketch

Reduce $p$ modulo $x_i^2 - x_i$ to its unique multilinear representative, which does not increase degree. The multilinear representative of OR is $1 - \prod_i (1 - x_i)$ (uniqueness of multilinear interpolation on the cube), whose top coefficient $\pm 1$ is nonzero in every nontrivial ring.

## Depends on

- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- R. Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", STOC 1987.
