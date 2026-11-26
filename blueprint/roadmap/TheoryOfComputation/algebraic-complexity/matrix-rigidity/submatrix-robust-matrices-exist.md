# Submatrix-robust matrices exist

A matrix is *submatrix-robust with deficiency $t$* if every square submatrix with $k$ rows and $k$ columns has rank at least $k-t$ (hence every $a\times b$ submatrix has rank at least $\min(a,b)-t$). For every $m$, some $m\times m$ matrix over $\mathbb{F}_2$ is submatrix-robust with deficiency $t=2\lfloor\sqrt m\rfloor+1$; moreover such a matrix can be chosen invertible.

## Proof sketch

A $k\times k$ block of rank $r$ is determined by $r$ spanning columns, the coefficients expressing the others, and the positions; counting shows that blocks of rank below $k-t$ occur in only a small fraction of all matrices when $t\approx2\sqrt m$, and a union bound over blocks leaves a robust matrix; a further counting argument keeps invertibility.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
