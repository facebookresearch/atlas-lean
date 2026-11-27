# Graphs defined by a first-order formula

Let $\delta(x, y)$ be a first-order formula over a vocabulary $\sigma$. In every $\sigma$-structure $\mathfrak{A}$ it defines the simple graph $G_\delta(\mathfrak{A})$ on $A$ in which distinct $a, b$ are adjacent iff $\mathfrak{A} \models \delta(a,b) \vee \delta(b,a)$. This is a one-dimensional first-order interpretation of the language of graphs in $\sigma$: every first-order sentence $\psi$ about graphs pulls back to a sentence $\psi^\delta$ over $\sigma$ with $\mathfrak{A} \models \psi^\delta$ iff $G_\delta(\mathfrak{A}) \models \psi$, and isomorphic structures define isomorphic graphs.

## Depends on

- [First-order interpretations](../first-order-interpretations-and-reductions/first-order-interpretations.md)

## Proof depends on

- [Pullback of formulas along interpretations](../first-order-interpretations-and-reductions/pullback-along-interpretations.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
