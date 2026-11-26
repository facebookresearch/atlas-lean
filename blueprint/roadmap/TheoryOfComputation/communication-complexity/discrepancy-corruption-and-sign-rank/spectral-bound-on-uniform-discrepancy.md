# Uniform discrepancy is bounded by the spectral norm of the sign matrix

Let $S$ be the real $X \times Y$ sign matrix with entries $(-1)^{f(x,y)}$ and let $\|S\|$ be its Euclidean operator norm. Under the uniform distribution,

$$\mathrm{disc}_{\mathrm{unif}}(f) \le \frac{\|S\|}{\sqrt{|X|\,|Y|}}.$$

For $n$-bit inputs on both sides this is $\|S\|/2^n$; for the inner product modulo two, $\|S\| = 2^{n/2}$, giving discrepancy at most $2^{-n/2}$.

## Proof sketch

For a rectangle $A \times B$, $\big|\mathbf{1}_A^{\mathsf T} S \mathbf{1}_B\big| \le \|S\| \sqrt{|A||B|} \le \|S\|\sqrt{|X||Y|}$; divide by $|X||Y|$.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
