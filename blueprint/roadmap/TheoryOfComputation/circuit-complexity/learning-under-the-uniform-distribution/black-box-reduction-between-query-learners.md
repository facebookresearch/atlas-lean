# Black-box reductions between membership-query learners multiply success probabilities

Let $\mathrm{amp}$ map Boolean functions on $\kappa$ coordinates to Boolean functions on $\iota$ coordinates, and suppose each value $\mathrm{amp}(f)(y)$ is computed by a decision tree $s_y$ of depth at most $d$ querying $f$. Let $A$ learn $\{\mathrm{amp}(f) : f \in C\}$ with error $\varepsilon'$, success probability $p$ and at most $q$ queries. Let a post-processing map $\mathrm{post}(h, \tau)$ with an extra uniform seed $\tau$ from a finite set satisfy: for every $f \in C$ and every $h$ with $\mathrm{err}(\mathrm{amp}(f), h) \le \varepsilon'$, at least a $\rho$ fraction of $\tau$ give $\mathrm{err}(f, \mathrm{post}(h,\tau)) \le \varepsilon$. Then the learner that runs $A$, answers each query $y$ by running $s_y$ on $f$, and outputs $\mathrm{post}(h,\tau)$ learns $C$ with error $\varepsilon$, success probability $p\rho$ and at most $qd$ queries.

## Proof sketch

Run on $f$, the simulated learner sees exactly the oracle $\mathrm{amp}(f)$, so its hypothesis is good with probability $p$; the extra seed is independent, so post-processing succeeds with conditional probability at least $\rho$. Each simulated query costs at most $d$ real queries.

## Depends on

- [Randomized membership-query learner as a family of decision trees](membership-query-learner.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
