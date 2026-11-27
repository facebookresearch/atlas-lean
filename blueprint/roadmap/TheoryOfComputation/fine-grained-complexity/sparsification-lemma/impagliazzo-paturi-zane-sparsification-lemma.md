# Impagliazzo–Paturi–Zane sparsification lemma

For every $k \ge 1$ and $\varepsilon > 0$ there is a constant $c = c(k,\varepsilon)$ such that every $k$-CNF formula $\varphi$ on $N$ variables can be written as $\varphi \equiv \bigvee_{i=1}^{t} \psi_i$ with $t \le 2^{\varepsilon N}$, where each $\psi_i$ is a $k$-CNF formula on the same variables in which every variable occurs in at most $c$ clauses, and every model of $\psi_i$ is a model of $\varphi$. The formulas $\psi_i$ can be enumerated in time $\mathrm{poly}(|\varphi|) 2^{\varepsilon N}$, and a disjoint variant gives $\#\varphi = \sum_i \#\psi_i$.

## Proof sketch

Run the sparsification branching (heart child or petal child at a heavy heart) until all leaves are sparse; in a sparse leaf every literal lies in fewer than $\theta_{c-1}$ clauses of each size $c\le k$, so every variable occurs in $O_k(\theta_{k-1})$ clauses. Every branch has length at most $L=O_k(\alpha^{2k-1}N)$ and at most $kN/\alpha$ petal steps, and a branch is determined by the positions of its petal steps, so the number of leaves is at most $\sum_{r\le kN/\alpha}\binom{L}{r}\le 2^{O_k(N\log\alpha/\alpha)}\le 2^{\varepsilon N}$ for $\alpha$ large enough. Each node costs polynomial time.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

- [Sparsification children cover the solutions](sparsification-children-cover-solutions.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001, Theorem 1 and Corollary 1.
- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
- C. Calabro, The Exponential Complexity of Satisfiability Problems, PhD thesis, University of California, San Diego, 2009.
