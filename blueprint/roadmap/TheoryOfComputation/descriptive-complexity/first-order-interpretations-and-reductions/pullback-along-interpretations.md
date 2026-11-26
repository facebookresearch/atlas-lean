# Pullback of formulas along interpretations

For every first-order interpretation $I$ of $\tau$ in $\sigma$ of dimension $d$ and every first-order formula $\psi(y_1,\dots,y_k)$ over $\tau$, there is a formula $\psi^I(\bar x_1,\dots,\bar x_k)$ over $\sigma$ such that for all $\sigma$-structures $\mathfrak{A}$ and tuples $\bar a_i$ in the domain of $I(\mathfrak{A})$, $\mathfrak{A} \models \psi^I(\bar a_1,\dots,\bar a_k) \iff I(\mathfrak{A}) \models \psi(\bar a_1,\dots,\bar a_k)$. It is obtained by replacing atoms by the defining formulas and relativizing quantifiers to $\delta$; if $I$ and $\psi$ are quantifier-free so is $\psi^I$, and interpretations compose.

## Proof sketch

Structural induction on $\psi$, with equality of target elements read as coordinatewise equality.

## Depends on

- [First-order interpretations](first-order-interpretations.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
