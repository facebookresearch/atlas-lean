# Hearts, flowers and petals of a clause set

Let $\psi$ be a reduced set of clauses (no clause strictly contains another) of width at most $k$, and let $\theta_1 \le \theta_2 \le \dots$ be thresholds. A set $H$ of $h \ge 1$ literals is a *heavy heart* for clause size $c > h$ if at least $\theta_{c-h}$ clauses of $\psi$ of size $c$ contain $H$; these clauses form the *flower* of $H$, and their differences $C \setminus H$ are its *petals*. $\psi$ is *sparse* (with respect to the thresholds) if it has no heavy heart. The two *children* of $\psi$ at a heavy heart $H$ are the reduced clause sets $\psi \cup \{H\}$ (the heart child) and $\psi \cup \{C \setminus H : C \text{ in the flower}\}$ (the petal child).

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001.
- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
- C. Calabro, The Exponential Complexity of Satisfiability Problems, PhD thesis, University of California, San Diego, 2009.
