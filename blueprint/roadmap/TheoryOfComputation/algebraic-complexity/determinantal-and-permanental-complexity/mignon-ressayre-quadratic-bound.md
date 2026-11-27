# Mignon–Ressayre: the determinantal complexity of the permanent is at least n^2/2

Over a field of characteristic zero, $\mathrm{dc}(\mathrm{per}_n)\ge n^2/2$.

## Proof sketch

If $\mathrm{per}_n=\det(L(x))$ with $L$ affine of size $m$, compare Hessians at a zero of the permanent where its Hessian has full rank $n^2$ (the Mignon–Ressayre point) with the Hessian of $\det_m$ at the corresponding singular matrix, whose rank is at most $2m$; since the Hessian of the composition is the pullback of the determinant's Hessian, $n^2\le 2m$.

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)
- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Proof depends on

- [The Hessian of the permanent at the Mignon–Ressayre point](hessian-of-the-permanent-at-mignon-ressayre-point.md)
- [The Hessian of the determinant at a singular matrix has rank at most 2m](hessian-of-the-determinant-at-singular-matrices.md)

## Sources

- Thierry Mignon, Nicolas Ressayre, "A quadratic bound for the determinant and permanent problem", International Mathematics Research Notices, 2004.
