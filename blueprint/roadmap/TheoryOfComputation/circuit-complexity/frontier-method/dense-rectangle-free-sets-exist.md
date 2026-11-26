# Dense rectangle-free sets exist

For every $n$ there is a set $S\subseteq\{0,1\}^n$ with $|S|\ge2^{n-1}$ that is $(n+2)$-rectangle-free. Likewise, by the same counting, most sets have small bias on all rectangles with sides at least $K_n$ once $K_n$ grows faster than $n$. Hence the hypotheses of the frontier lower bounds are satisfiable, and those bounds hold for most Boolean functions in an explicit-counting sense.

## Proof sketch

A rectangle with both sides of size exactly $K$ is determined by a cut and $K$ spanning inputs, so there are at most $2^n(2^n)^K$ of them, each with $K^2$ points; a uniformly random set contains a given one with probability $2^{-K^2}$. So at most a $2^{n+nK-K^2}$ fraction of all sets contain one, which is at most $2^{-n-4}$ for $K=n+2$, while at least half of all sets have at least $2^{n-1}$ elements.

## Depends on

- [Rectangle-free sets and rectangle bias](rectangle-free-sets-and-rectangle-bias.md)

## Sources

- Noga Alon, Joel H. Spencer, "The Probabilistic Method", Wiley, 2016.
- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
