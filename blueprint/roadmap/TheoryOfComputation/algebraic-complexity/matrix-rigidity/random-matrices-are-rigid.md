# Random matrices over a finite field are highly rigid

Let $K$ be a finite field with $q$ elements, $n\ge1$ and $0\le r\le n$. For every integer $t\ge1$ with $t\le(n-r)^2/(4\log_qn+2)$, a uniformly random $n\times n$ matrix $A$ over $K$ satisfies

$$
\Pr\bigl[R_A(r)<t\bigr]\le4t\,q^{-(n-r)^2/2} .
$$

In particular, for fixed $q$ and $r\le(1-\varepsilon)n$, almost all matrices have rigidity $R_A(r)=\Omega((n-r)^2/\log n)$.

## Proof sketch

Count matrices within fewer than $t$ changes of a matrix of rank at most $r$: such a matrix has its columns in some $r$-dimensional subspace, one of at most $3.5\,q^{r(n-r)}$, so there are at most $3.5\,q^{r(2n-r)}$ of them; and there are at most $t\,(n^2q)^{t-1}\le t\,q^{(t-1)(2\log_qn+1)}$ ways to change fewer than $t$ entries. For $t$ as stated the product is at most $4t\,q^{n^2-(n-r)^2/2}$, since $r(2n-r)=n^2-(n-r)^2$.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Leslie G. Valiant, "Graph-Theoretic Arguments in Low-Level Complexity", Mathematical Foundations of Computer Science 1977, 1977.
