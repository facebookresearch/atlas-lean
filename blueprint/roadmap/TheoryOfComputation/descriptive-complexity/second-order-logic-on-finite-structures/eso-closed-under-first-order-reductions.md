# ESO definability is closed under first-order reductions

Let $I$ be a first-order interpretation of dimension $d$ of $\tau$ in $\sigma$ and $\Phi = \exists R_1\cdots R_m\, \varphi$ an ESO sentence over $\tau$. Then there is an ESO sentence $\Phi^I$ over $\sigma$, in which a relation variable of arity $r$ becomes one of arity $rd$, such that $\mathfrak{A} \models \Phi^I$ iff $I(\mathfrak{A}) \models \Phi$. Hence if $K \le_{\mathrm{fo}} K'$ and $K'$ is ESO-definable then so is $K$.

## Proof sketch

Pull back the first-order matrix along the extension of $I$ that interprets each $R_i$ by a new relation variable on blocks of $d$ coordinates; expansions of $I(\mathfrak{A})$ correspond to expansions of $\mathfrak{A}$ restricted to domain tuples.

## Depends on

- [Relational second-order logic on finite structures](relational-second-order-logic.md)
- [First-order and quantifier-free reductions](../first-order-interpretations-and-reductions/first-order-reductions.md)

## Proof depends on

- [Pullback of formulas along interpretations](../first-order-interpretations-and-reductions/pullback-along-interpretations.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
