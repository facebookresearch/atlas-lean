# Best-of-k selection boosts the confidence of a membership-query learner

Let $A$ be a randomized membership-query learner that, for every $f \in C$, has error above $\varepsilon$ with probability at most $\delta$ over its seed and makes at most $q$ queries. The best-of-$k$ learner runs $A$ on $k$ independent seeds, estimates the agreement of each of the $k$ hypotheses with $f$ on $t$ fresh uniform points by membership queries, and outputs a hypothesis of largest empirical agreement. Then for every $\theta \ge 0$ it has error above $\varepsilon + 2\theta$ with probability at most

$$
\delta^k + 2k\,e^{-2t\theta^2},
$$

makes at most $kq + t$ queries, and always outputs the hypothesis of one of the runs, so any bound on all runs' hypotheses (such as circuit size) bounds its output.

## Proof sketch

All $k$ runs fail with probability at most $\delta^k$. Otherwise some run has error at most $\varepsilon$; by Hoeffding each of the $k$ agreement estimates is within $\theta$ of the truth except with probability $2e^{-2t\theta^2}$, and on this event the selected hypothesis has error at most $\varepsilon + 2\theta$.

## Depends on

- [Randomized membership-query learner as a family of decision trees](membership-query-learner.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
