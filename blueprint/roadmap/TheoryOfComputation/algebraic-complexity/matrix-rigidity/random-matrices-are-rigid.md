# Random matrices over a finite field are highly rigid

Let $K$ be a finite field, $n\ge1$ and $0\le r\le n$. A uniformly random $n\times n$ matrix $A$ over $K$ satisfies

$$
R_A(r)\ge\Bigl\lfloor\frac{(n-r)^2}{4\lfloor\log_{|K|}n\rfloor+6}\Bigr\rfloor
$$

with probability greater than $1-|K|^{-\lfloor(n-r)^2/2\rfloor}$. In particular, for fixed $|K|$ and $r\le(1-\varepsilon)n$, almost all matrices have rigidity $\Omega((n-r)^2/\log n)$.

## Proof sketch

Count matrices within distance $t$ of a rank-$r$ matrix: there are $O(|K|^{r(2n-r)})$ matrices of rank at most $r$ (a rank-$r$ matrix is determined by its column space, one of $O(|K|^{r(n-r)})$ subspaces, and an $r\times n$ coefficient matrix), and at most $\binom{n^2}{t}|K|^t$ ways to change $t$ entries; for $t$ as stated the product is a tiny fraction of $|K|^{n^2}$.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Leslie G. Valiant, "Graph-Theoretic Arguments in Low-Level Complexity", Mathematical Foundations of Computer Science 1977, 1977.
