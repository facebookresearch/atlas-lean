# Rigidity of totally regular matrices

Let $A$ be an $n\times n$ totally regular matrix (all square submatrices nonsingular; for example a Cauchy matrix). Then for $\log_2^2 n\le r\le n/2$,

$$
R_A(r)\ge\frac{n^2}{4(r+1)}\log_2\frac nr .
$$

## Proof sketch

After changing a set of entries to reach rank $r$, every $(r+1)\times(r+1)$ submatrix avoiding the changed entries would be singular, contradicting total regularity; so the changed positions must hit every $(r+1)\times(r+1)$ all-ones pattern, and a Zarankiewicz-type (Kővári–Sós–Turán) counting bound on bipartite graphs without $K_{r+1,r+1}$ gives the estimate.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Totally regular matrices and Cauchy matrices](../../../LinearAlgebra/special-matrices/structured-matrices-in-complexity/totally-regular-and-cauchy-matrices.md)

## Sources

- Joel Friedman, "A note on matrix rigidity", Combinatorica, 1993.
- M. Amin Shokrollahi, Daniel A. Spielman, Volker Stemann, "A remark on matrix rigidity", Information Processing Letters, 1997.
- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
