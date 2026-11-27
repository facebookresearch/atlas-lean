# Deterministic extraction fails even with one bit of entropy deficiency

For all $n, m \ge 1$ and every function $f : \{0,1\}^n \to \{0,1\}^m$ there is a source $X$ on $\{0,1\}^n$ with min-entropy at least $n - 1$ such that the first output bit of $f(X)$ is constant and $f(X)$ is at statistical distance at least $1/2$ from uniform on $\{0,1\}^m$. Hence no deterministic function is an $(n-1, \varepsilon)$-extractor (with a one-element seed set) for $\varepsilon < 1/2$; in particular no function to $\{0,1\}$ extracts from all sources missing one bit of min-entropy.

## Proof sketch

Some value $b$ of the first output bit has at least $2^{n-1}$ preimages; let $X$ be uniform on that set. Then $X$ has min-entropy at least $n-1$, the first bit is constantly $b$, and the event "first bit $\ne b$" has probability $1/2$ under uniform but $0$ under $f(X)$.

## Depends on

- [Seeded randomness extractors](seeded-randomness-extractors.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 21 (Chapter 16, Exercise 7 of the January 2007 web draft).
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012, Proposition 6.11.
