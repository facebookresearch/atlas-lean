# Branch length bound in the sparsification tree

Fix $k \ge 1$, $\alpha \ge 1$, $X = 2k\alpha$ and thresholds $\theta_0 = 1$, $\theta_j = \alpha X^{2j-1}$. Along every branch of the sparsification tree started from a clause set over $N$ variables, at most $N X^{2c-1}$ clauses of size $c$ are introduced (as hearts or petals), and every introduced clause is new and distinct from clauses introduced at other steps. Hence every branch has length at most $\sum_{c \le k} N X^{2c-1} = O_k(\alpha^{2k} N)$, and on a branch the number of heart steps is at most a $1/\alpha$-fraction of its length.

## Proof sketch

Induction on the clause size $c$: a new clause of size $c$ that is deleted later is charged to a heavy heart of smaller size, and the threshold products $\theta_{c-h} X^{2h-1}$ all equal $\alpha X^{2c-2}$, which telescopes into the stated bound.

## Depends on

- [Hearts, flowers and petals of a clause set](hearts-flowers-and-petals.md)

## Proof depends on

- [Sparsification children cover the solutions](sparsification-children-cover-solutions.md)

## Sources

- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
- C. Calabro, The Exponential Complexity of Satisfiability Problems, PhD thesis, University of California, San Diego, 2009.
