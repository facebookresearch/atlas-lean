# Impagliazzo–Paturi–Zane sparsification lemma

For every $k \ge 1$ and $\varepsilon > 0$ there is a constant $c = c(k,\varepsilon)$ such that every $k$-CNF formula $\varphi$ on $N$ variables can be written as $\varphi \equiv \bigvee_{i=1}^{t} \psi_i$ with $t \le 2^{\varepsilon N}$, where each $\psi_i$ is a $k$-CNF formula on the same variables in which every variable occurs in at most $c$ clauses, and every model of $\psi_i$ is a model of $\varphi$. The formulas $\psi_i$ can be enumerated in time $\mathrm{poly}(|\varphi|) 2^{\varepsilon N}$, and a disjoint variant gives $\#\varphi = \sum_i \#\psi_i$.

## Proof sketch

Run the sparsification branching (heart child or petal child at a heavy heart) until all leaves are sparse; sparse leaves have every variable in $O_k(\theta_k)$ clauses. The branch analysis bounds the number of heart steps on a branch by $O(N/\alpha)$-ish quantities, so with $\alpha$ large the number of leaves is $\binom{L}{\le L/\alpha} \le 2^{\varepsilon N}$.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

- [Sparsification children cover the solutions](sparsification-children-cover-solutions.md)
- [Branch length bound in the sparsification tree](branch-length-bound-in-sparsification.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001.
- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
- C. Calabro, The Exponential Complexity of Satisfiability Problems, PhD thesis, University of California, San Diego, 2009.
