# The Hessian of the determinant at a singular matrix has rank at most 2m

Let $X$ be an $m\times m$ matrix with $\det X=0$. Then the Hessian of the generic determinant $\det_m$ at $X$ (an $m^2\times m^2$ matrix of second partial derivatives) has rank at most $2m$; if moreover $\operatorname{rank}X\le m-3$, the Hessian vanishes.

## Proof sketch

Second partial derivatives of $\det$ are signed $(m-2)$-minors. Moving $X$ by row and column operations to $\mathrm{diag}(0,1,\dots,1)$ in the corank-one case, the only nonzero second derivatives involve the first row or the first column, giving rank at most $2m$; in higher corank all $(m-2)$-minors vanish or the support is smaller.

## Depends on

- [Leibniz formula for the determinant](../../../LinearAlgebra/determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/det-apply.md)
- [Jacobi's formula](../../../LinearAlgebra/determinants-and-matrix-identities/jacobi-s-formula/jacobi-det-derivative.md)

## Sources

- Thierry Mignon, Nicolas Ressayre, "A quadratic bound for the determinant and permanent problem", International Mathematics Research Notices, 2004.
