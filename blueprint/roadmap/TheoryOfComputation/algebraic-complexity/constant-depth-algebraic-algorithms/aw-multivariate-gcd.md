# Andrews–Wigderson: multivariate GCD of polynomials given by constant-depth circuits

Over fields of characteristic $0$, if $f, g \in \mathbb{F}[x_1, \dots, x_n]$ of degree at most $d$ are computed by constant-depth arithmetic circuits of size $s$, then $\gcd(f, g)$ and the squarefree decomposition of $f$ are computed by constant-depth arithmetic circuits of size $\operatorname{poly}(s, n, d)$ (randomized constructions; deterministic under derandomization of polynomial identity testing for constant-depth circuits, which by the Limaye-Srinivasan-Tavenas lower bound holds in subexponential time).

## Proof sketch

Apply a random invertible linear change of variables so that $f$ becomes monic in $x_1$, then treat $f, g$ as univariate polynomials in $x_1$ over the field of rational functions in the remaining variables and apply the univariate constant-depth GCD formulas symbolically; the coefficients are constant-depth circuits in $x_2, \dots, x_n$ and the formulas compose with constant blow-up in depth.

## Depends on

- [Constant-depth arithmetic formulas with unbounded fan-in (arithmetic AC0)](constant-depth-arithmetic-formula.md)

## Proof depends on

- [Andrews–Wigderson: the GCD of two polynomials in arithmetic AC0](aw-gcd-ac0.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839.
- N. Limaye, S. Srinivasan, S. Tavenas, "Superpolynomial lower bounds against low-depth algebraic circuits", FOCS (2021); Communications of the ACM 65 (2022), ECCC TR21-081.
