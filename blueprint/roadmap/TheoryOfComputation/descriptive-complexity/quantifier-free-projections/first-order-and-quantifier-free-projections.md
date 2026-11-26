# First-order and quantifier-free projections

A *first-order projection* (Immerman–Landau) is a full-tuple ordered interpretation of positive dimension in which each output relation is defined by a disjunction of mutually exclusive numeric cases $\alpha_i(\bar x)$, each guarding a single input literal or constant: $\varphi_R(\bar x) = \bigvee_i (\alpha_i(\bar x) \wedge \lambda_i(\bar x))$ where the $\alpha_i$ mention only numeric predicates and each $\lambda_i$ is an atom, a negated atom, $\top$ or $\bot$. Each output bit is thus an input bit, its negation or a constant, chosen by numeric information alone, as in Valiant's projections. A *quantifier-free projection* (qfp) additionally requires all $\alpha_i$ to be quantifier-free formulas over $\le$, successor, $0$ and $\max$ (without $\mathrm{BIT}$). The reductions are written $\le_{\mathrm{fop}}$ and $\le_{\mathrm{qfp}}$.

## Depends on

- [Ordered first-order interpretations and first-order queries](../ordered-structures-and-arithmetic/ordered-first-order-interpretations.md)

## Sources

- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
- N. Immerman, Descriptive Complexity, Springer, 1999.
