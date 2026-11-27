# Simulating unbounded fan-in by fan-in two

A conjunction or disjunction of $k\ge 1$ arguments is computed by a balanced tree of $k-1$ binary gates of the same kind and depth $\lceil\log_2 k\rceil$. Consequently every circuit over the unbounded fan-in basis $\{\neg,\bigwedge,\bigvee\}$ with $s$ gates, depth $d$ and total fan-in (number of wires) $w$ has an equivalent De Morgan circuit of fan-in two with at most $w$ binary gates and depth at most $d\max(1,\lceil\log_2 w\rceil)$.

## Proof sketch

Replace each gate of fan-in $k$ by a balanced binary tree; sizes add and depth multiplies by at most the logarithm of the largest fan-in.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [Unbounded fan-in signature](../../../unbounded-fan-in-circuits/ac-signature.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
