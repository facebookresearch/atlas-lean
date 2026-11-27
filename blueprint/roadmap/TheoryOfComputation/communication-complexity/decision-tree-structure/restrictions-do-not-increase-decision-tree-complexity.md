# Restrictions and post-processing do not increase decision tree complexity

For every $f : \{0,1\}^n \to \beta$, every restriction $\rho$ and every map $h : \beta \to \gamma$: $D(f|_\rho) \le D(f)$ and $D(h \circ f) \le D(f)$, with equality when $h$ is injective (e.g. negation). Restricted parity still requires querying every free bit: $D(\mathrm{PARITY}|_\rho)$ equals the number of free variables of $\rho$.

## Proof sketch

Answer the queries of $\rho$'s fixed variables inside a tree for $f$; relabel leaves by $h$. Parity restricted to free variables is a parity (or its negation) on them, and parity is sensitive to every bit at every input.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
