# Branch length bound in the sparsification tree

Fix $k \ge 1$, $\alpha \ge 1$, $X = 2k\alpha$ and thresholds $\theta_0 = 1$, $\theta_j = \alpha X^{2j-1}$. Suppose each node of the sparsification tree branches on a heavy heart chosen with the smallest clause size $c$ and, for that $c$, the largest heart size $h$ (the priority of Calabro, Impagliazzo and Paturi, which is also the loop order of Impagliazzo, Paturi and Zane's procedure). Then along every branch of the tree started from a clause set over $N$ variables, at most $N X^{2c-1}$ clauses of size $c$ are introduced (as hearts or petals), and every introduced clause is new and distinct from clauses introduced at other steps. Hence every branch has length at most $\sum_{c \le k} N X^{2c-1} = O_k(\alpha^{2k-1} N)$, since every step introduces at least one new clause. A petal step whose petals have size $p$ introduces at least $\theta_p = \alpha X^{2p-1}$ new clauses of size $p$, so each branch has at most $N/\alpha$ petal steps per petal size and at most $kN/\alpha$ petal steps in total; the remaining steps are heart steps.

Without this priority the bound fails: for $N=1000$, $k=3$, $\alpha=1$ and all triples $\{u,x_i,x_j\}$ through one literal $u$, branching on the heart $\{u\}$ adds $498{,}501$ petals of size $2$, more than $N X^{3}=216{,}000$.

## Proof sketch

Induction on the clause size $c$ (Impagliazzo–Paturi–Zane, Lemmas 3–6): a new clause of size $c$ either survives to the sparse leaf, where each literal lies in fewer than $\theta_{c-1}$ clauses of size $c$, or is eliminated by a later new clause of some size $h<c$, which eliminates at most about $2\theta_{c-h}$ clauses of size $c$. This uses the priority (as in Impagliazzo–Paturi–Zane, Lemma 3): when petals of size $p \ge 2$ are added, no literal lies in $\theta_{p-1}$ of them, since otherwise a larger heart for the same clause size would be heavy. The products $\theta_{c-h} X^{2h-1}$ all equal $\alpha X^{2c-2}$, so the sum is at most $N X^{2c-1}$. Dividing the number of new petals of size $p$ by $\theta_p$ bounds the petal steps.

## Depends on

- [Hearts, flowers and petals of a clause set](hearts-flowers-and-petals.md)

## Proof depends on

- [Sparsification children cover the solutions](sparsification-children-cover-solutions.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001, Lemmas 3–7.
- C. Calabro, R. Impagliazzo and R. Paturi, "A Duality between Clause Width and Clause Density for SAT", 21st IEEE Conference on Computational Complexity (CCC), 2006.
- C. Calabro, The Exponential Complexity of Satisfiability Problems, PhD thesis, University of California, San Diego, 2009.
