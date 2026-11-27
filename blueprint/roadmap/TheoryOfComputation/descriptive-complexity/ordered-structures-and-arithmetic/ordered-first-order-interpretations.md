# Ordered first-order interpretations and first-order queries

An *ordered interpretation* of dimension $k$ from canonically ordered $\sigma$-structures to $\tau$-structures consists of a domain formula $\delta(\bar x)$ and formulas for the input relations of $\tau$, all over $\sigma$ plus the numeric vocabulary. Its image on $\mathfrak{A}$ has universe the $k$-tuples satisfying $\delta$, renumbered by lexicographic rank onto $\{0,\dots,m-1\}$, with canonical numeric predicates. It is a *first-order query* if moreover the order, $\mathrm{BIT}$ and the constants of the image are first-order definable over the source on domain tuples (automatic when $\delta$ is $\top$, the *full-tuple* case). First-order queries compose, and $K \le_{\mathrm{fo}} K'$ on ordered structures means some first-order query maps members of $K$ exactly to members of $K'$.

## Depends on

- [Canonically ordered structures with BIT](canonically-ordered-structures-with-bit.md)
- [First-order interpretations](../first-order-interpretations-and-reductions/first-order-interpretations.md)

## Proof depends on

- [Lexicographic order, successor and BIT on tuples are definable](lexicographic-tuple-numeric-predicates.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
