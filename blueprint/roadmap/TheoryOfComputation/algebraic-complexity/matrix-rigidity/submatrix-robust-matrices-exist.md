# Submatrix-robust matrices exist

A matrix is *submatrix-robust with deficiency $t$* if every square submatrix with $k$ rows and $k$ columns has rank at least $k-t$ (hence every $a\times b$ submatrix has rank at least $\min(a,b)-t$). For every $m$, some $m\times m$ matrix over $\mathbb{F}_2$ is submatrix-robust with deficiency $t=2\lfloor\sqrt m\rfloor+1$; moreover such a matrix can be chosen invertible.

## Proof sketch

For a uniformly random matrix over $\mathbb{F}_2$, a fixed $k\times k$ block has rank below $k-t$ with probability at most $7\cdot2^{-(t+1)^2}$, by counting matrices of each rank through their column spaces. There are $\sum_k\binom mk^2\le4^m$ square blocks, and $(t+1)^2\ge4m$, so some block fails with probability at most $7\cdot2^{-2m}$, which for $m\ge3$ is below the probability (at least $0.28$) that the matrix is invertible; for $m\le2$ the deficiency is at least the size of every block.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
