# First-order interpretations, first-order reductions and quantifier-free projections

A **$k$-dimensional first-order interpretation** $I$ from $\sigma$-structures to $\tau$-structures is given by first-order $\sigma$-formulas: a formula defining the new universe as a set of $k$-tuples (lexicographically ordered), and for each $r$-ary symbol $R\in\tau$ a formula with $kr$ free variables defining $R$ on those tuples. A query $A$ **first-order reduces** to $B$ if some interpretation $I$ satisfies $\mathcal{A}\in A\iff I(\mathcal{A})\in B$. A **quantifier-free projection** is an interpretation whose defining formulas are quantifier-free and in which each tuple of the new relations is determined by a single literal of the input or a constant (BIT-free if BIT is not used). Every first-order reduction is computable in logarithmic space, and first-order reductions compose.

## Depends on

- [Ordered finite structures with built-in numerical predicates](ordered-structures-with-bit.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999.
- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
