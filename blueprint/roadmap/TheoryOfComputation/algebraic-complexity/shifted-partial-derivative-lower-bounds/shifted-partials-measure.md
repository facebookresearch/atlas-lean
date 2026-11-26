# The dimension of shifted partial derivatives

For $f \in \mathbb{F}[x_1, \dots, x_n]$ and integers $k, \ell \ge 0$, let $\partial^{=k} f$ be the set of all $k$-th order partial derivatives $\partial^{\alpha} f$ with $|\alpha| = k$, and $\mathbf{x}^{=\ell}$ the set of monomials of degree exactly $\ell$. The **shifted partials measure** is

$$
\mathrm{SP}_{k,\ell}(f) = \dim_{\mathbb{F}} \operatorname{span}\bigl\{\, m \cdot g \;:\; m \in \mathbf{x}^{=\ell},\ g \in \partial^{=k} f \,\bigr\}.
$$

It is subadditive: $\mathrm{SP}_{k,\ell}(f + g) \le \mathrm{SP}_{k,\ell}(f) + \mathrm{SP}_{k,\ell}(g)$, and the trivial upper bound is $\binom{n + \ell + d - k - 1}{n - 1}$ for $f$ homogeneous of degree $d$.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- N. Kayal, "An exponential lower bound for the sum of powers of bounded degree polynomials", ECCC TR12-081 (2012).
- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Approaching the chasm at depth four", Journal of the ACM 61 (2014); CCC (2013).
- R. Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9 (2021), github survey.
