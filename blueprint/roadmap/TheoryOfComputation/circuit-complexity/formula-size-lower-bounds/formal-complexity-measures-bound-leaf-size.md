# Formal complexity measures lower-bound formula leaf size

If $\mu$ is a formal complexity measure, then every De Morgan formula without constant leaves computing $f$ has at least $\mu(f)$ leaves: $\mu(f)\le L(f)$.

## Proof sketch

Induction on the formula: literals have measure at most one and each AND or OR gate is subadditive; negations can be pushed to the leaves without changing the leaf count.

## Depends on

- [Formal complexity measures](formal-complexity-measures.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
