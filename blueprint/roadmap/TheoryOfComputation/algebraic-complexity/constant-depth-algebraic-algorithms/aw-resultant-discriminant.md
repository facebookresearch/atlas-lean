# Andrews–Wigderson: resultants, discriminants and Bézout coefficients in arithmetic AC0

Over fields of characteristic $0$ or sufficiently large characteristic, the resultant $\operatorname{Res}(f, g)$ and the discriminant $\operatorname{Disc}(f)$ of univariate polynomials of degree at most $n$, the Bézout coefficients $u, v$ with $uf + vg = \gcd(f,g)$, the squarefree decomposition of $f$, and the inverses of nonsingular Sylvester and Bézout matrices are all computed by constant-depth arithmetic formulas of size $\operatorname{poly}(n)$ (for outputs that depend on the degree of the GCD, one formula per possible degree, as in the GCD theorem).

## Proof sketch

$\operatorname{Res}(f,g) = \prod_i g(r_i)$ is a symmetric function of the roots of $f$; its logarithm is a power-sum expression, so exponentiating a truncated series computes it in constant depth. The discriminant is the resultant of $f$ and $f'$. Bézout coefficients and structured matrix inverses are obtained from the GCD formulas by expressing them as symmetric rational functions of roots with denominators given by resultants.

## Depends on

- [Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Andrews–Wigderson: the GCD of two polynomials in arithmetic AC0](aw-gcd-ac0.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
