# Every SO∃-Horn sentence is equivalent to an FO(LFP) sentence

For every SO∃-Horn sentence over $\sigma$ there is an FO(LFP) sentence over $\sigma$ equivalent to it on every structure in which two closed terms denote distinct elements (in particular on all ordered structures with $0 \ne \max$). The relation variables of different arities are packed into one fixed-point relation with tags, the least fixed point computes the least model of the definite clauses, and the goal clauses are checked against it by a first-order formula.

## Proof sketch

Simultaneous induction reduces to a single least fixed point using two distinct constants as tags for the components; the immediate-consequence operator of the definite clauses is positive in the recursion variable.

## Depends on

- [Existential second-order Horn logic](existential-second-order-horn-logic.md)
- [Formulas of first-order logic with least fixed points](../immerman-vardi-theorem/ogfo.md)

## Proof depends on

- [SO∃-Horn sentences are decided by the least model](so-horn-least-model.md)
- [Least fixed points of positive operators stabilize in polynomially many stages](../fixed-point-and-closure-logics/least-fixed-point-stages.md)

## Sources

- E. Grädel, "Capturing Complexity Classes by Fragments of Second-Order Logic", Theoretical Computer Science 101(1), 35–57, 1992.
- N. Immerman, Descriptive Complexity, Springer, 1999.
