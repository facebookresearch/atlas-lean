# Every n × n matrix has rigidity at most (n - r)^2

For every $n\times n$ matrix $A$ over a field and every $0\le r\le n$, $R_A(r)\le(n-r)^2$; more generally an $m\times n$ matrix has $R_A(r)\le(m-r)(n-r)$ for $r\le\min(m,n)$. The bound is attained, for example, by the $2\times2$ Hadamard matrix at $r=0$ and $r=1$ over any field of characteristic other than $2$.

## Proof sketch

If $\operatorname{rank}A\le r$ nothing changes. Otherwise permute so that the top-left $r\times r$ block is nonsingular; replacing the bottom-right $(m-r)\times(n-r)$ block by the Schur-complement-compatible values $CA_{11}^{-1}B$ yields rank exactly $r$.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Leslie G. Valiant, "Graph-Theoretic Arguments in Low-Level Complexity", Mathematical Foundations of Computer Science 1977, 1977.
