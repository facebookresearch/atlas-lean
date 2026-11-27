# Fixing the random seed of a multi-output circuit

Let $C$ be a circuit reading $x\in\{0,1\}^n$ and a seed $r\in\{0,1\}^p$, and let $\mathrm{Correct}(x,\cdot)$ be a set of acceptable outputs for each $x$ (several answers may be acceptable). If for every $x$ fewer than a $2^{-n}$ fraction of the seeds $r$ give $C(x,r)\notin\mathrm{Correct}(x)$, then some fixed seed $r^*$ makes $C(x,r^*)$ correct for every $x$ simultaneously, and hard-wiring it gives a deterministic circuit of size at most $|C|+2$ (two constant gates) and depth one larger.

## Proof sketch

Union bound over the $2^n$ inputs: the bad seeds of all inputs together form fewer than $2^p$ seeds.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Leonard Adleman, "Two Theorems on Random Polynomial Time", 19th Annual Symposium on Foundations of Computer Science, 75–83, 1978.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
