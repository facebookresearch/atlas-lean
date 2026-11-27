# Rigidity of totally regular matrices

Let $A$ be an $n\times n$ totally regular matrix over a field (all square submatrices nonsingular; for example a Cauchy matrix $(1/(x_i+y_j))_{i,j}$). Then

$$
R_A(r) = \Omega\Bigl(\frac{n^2}{r}\log\frac nr\Bigr) \qquad \text{for } \log_2^2 n\le r\le n/2 .
$$

Explicitly, for all sufficiently large $n$ and all $r$ with $\log_2^2 n\le r+1\le n/2$, $R_A(r)\ge\frac{n^2}{4(r+1)}\log_2\frac nr$.

## Proof sketch

After changing a set of entries to reach rank at most $r$, every $(r+1)\times(r+1)$ submatrix avoiding the changed entries would be singular, contradicting total regularity; so the changed positions must hit every $(r+1)\times(r+1)$ submatrix. A Zarankiewicz-type (Kővári–Sós–Turán) count on bipartite graphs without $K_{k,k}$ shows that, for $\log^2 n\le k\le n/2$ and $n$ sufficiently large, fewer than $\frac{n^2}{4k}\log\frac{n}{k-1}$ marked entries of an $n\times n$ matrix always leave a $k\times k$ submatrix unmarked; take $k = r+1$.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Totally regular matrices and Cauchy matrices](../../../LinearAlgebra/special-matrices/structured-matrices-in-complexity/totally-regular-and-cauchy-matrices.md)

## Sources

- M. Amin Shokrollahi, Daniel A. Spielman, Volker Stemann, "A remark on matrix rigidity", Information Processing Letters 64(6), 283–285, 1997: Lemma 2.1, Corollary 2.2 (for $\log^2 n \le r \le n/2$ and $n$ sufficiently large) and Theorem 3.1 (the Cauchy case, derived from Corollary 2.2 using only that every square submatrix is nonsingular).
- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
