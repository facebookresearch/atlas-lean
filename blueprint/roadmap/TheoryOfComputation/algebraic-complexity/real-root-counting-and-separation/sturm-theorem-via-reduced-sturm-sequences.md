# Sturm's theorem for arbitrary nonzero real polynomials via reduced Sturm sequences

Let $p\in\mathbb{R}[X]$ be nonzero (not necessarily squarefree), $g=\gcd(p,p')$, and let $\mathrm{Var}(x)$ be the number of sign changes at $x$ of the Sturm sequence of $(p/g,\ p'/g)$. Then for all real $a\le b$, $\mathrm{Var}(a)-\mathrm{Var}(b)$ equals the number of distinct real roots of $p$ in the half-open interval $(a,b]$, with no assumption that $p(a)\neq0$ or $p(b)\neq0$.

## Proof sketch

Dividing by $\gcd(p,p')$ gives a squarefree polynomial with the same distinct roots, and the reduced sequence is the Sturm chain of that polynomial up to a common factor that does not affect sign changes away from roots; the half-open form follows by analyzing sign changes at a root endpoint (only the right endpoint's root is counted).

## Depends on

- [Sturm's theorem](../../../Algebra/zeros-of-polynomials/sturm-s-theorem/sturm.md)
- [Sturm chain](../../../Algebra/zeros-of-polynomials/sturm-s-theorem/sturm-chain.md)

## Sources

- Saugata Basu, Richard Pollack, Marie-Françoise Roy, "Algorithms in Real Algebraic Geometry", Springer, 2006.
