# Random Boolean functions remain nonconstant on all large subcubes

Fix $\varepsilon\in(0,1)$. Let $f$ be a uniformly random Boolean function on $n$ bits. Then the probability that every partial assignment fixing at most $n-n^\varepsilon$ coordinates leaves a nonconstant function tends to $1$ as $n\to\infty$. (This is the largeness condition of the restriction-based natural property used against $\mathsf{AC}^0$.)

## Proof sketch

A subcube with $k\ge n^\varepsilon$ free coordinates is constant with probability $2^{1-2^k}$. There are at most $3^n$ subcubes, and $3^n\cdot 2^{1-2^{n^\varepsilon}}\to 0$.

## Depends on

- [Natural property](../../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences, 1997.
