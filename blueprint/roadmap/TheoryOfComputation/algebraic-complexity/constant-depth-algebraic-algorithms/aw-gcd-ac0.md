# Andrews–Wigderson: the GCD of two polynomials in arithmetic AC0

Let $\mathbb{F}$ be a field of characteristic $0$ or sufficiently large characteristic. There are constant-depth arithmetic formulas of size $\operatorname{poly}(n)$ that, on input the coefficient vectors of two univariate polynomials $f, g$ of degree at most $n$ (with $f$ monic), output the coefficients of the monic $\gcd(f, g)$; more precisely, for every $e \le n$ there is such a formula $F_e$ that is correct on every input pair with $\deg \gcd(f,g) = e$, and the degree $e$ is detected by the vanishing pattern of constant-depth computable subresultants.

## Proof sketch

Express the GCD through the roots of $f$ shared with $g$: the polynomial $\prod_{i}(t - r_i)^{[g(r_i) = 0]}$. Symmetric functions of the roots weighted by the vanishing pattern of $g$ are computed via power sums of $r_i$ times functions of $g(r_i)$, which are themselves symmetric in the roots and hence polynomials in the coefficients computable in constant depth. Rank detection of Sylvester-type matrices in constant depth determines the GCD degree, selecting the correct formula.

## Depends on

- [Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Constant-depth formulas for power sums of roots](power-sums-from-coefficients.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
