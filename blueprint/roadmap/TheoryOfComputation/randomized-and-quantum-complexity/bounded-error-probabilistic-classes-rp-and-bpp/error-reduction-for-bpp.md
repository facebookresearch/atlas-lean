# Error reduction for BPP

Let $L \in \mathsf{BPP}$ be decided by a probabilistic polynomial-time machine with error probability at most $1/3$ on every input. For every polynomial $q$ there is a probabilistic polynomial-time machine deciding $L$ with error probability at most $2^{-q(n)}$ on inputs of length $n$: run the original machine $O(q(n))$ times independently and output the majority answer, whose error is bounded by a Chernoff bound (for $k$ runs, at most $e^{-k/18}$). Similarly, for $L \in \mathsf{RP}$, accepting if any of $q(n)$ independent runs accepts reduces the one-sided error to $2^{-q(n)}$.

## Depends on

- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, <https://theory.cs.princeton.edu/complexity/>, Theorem 7.10
