# Sparsification children cover the solutions

For a heavy heart $H$ with flower $\Phi$, an assignment satisfies $\psi$ if and only if it satisfies the heart child or the petal child: if all literals of $H$ are false then every flower clause must be satisfied by its petal, and otherwise $H$ is satisfied. Each child accepts only assignments accepted by $\psi$. In the counting variant, adding to the petal child the unit clauses negating $H$ makes the two children disjoint, so their model counts add up to that of $\psi$.

## Proof sketch

Case split on whether the assignment satisfies the clause $H$.

## Depends on

- [Hearts, flowers and petals of a clause set](hearts-flowers-and-petals.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001.
- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
