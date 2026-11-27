# Huang-Kueng-Preskill: classical shadows predict many properties from few measurements

Let $O_1, \dots, O_M$ be observables, $\varepsilon, \delta \in (0,1)$, and

$$
N = O\!\left( \frac{\log(M/\delta)}{\varepsilon^2} \max_{i} \left\| O_i - \tfrac{\mathrm{Tr}(O_i)}{2^n} I \right\|^2_{\mathrm{shadow}} \right).
$$

From $N$ independent classical shadow snapshots of $\rho$, the median-of-means estimators $\hat o_i$ satisfy $|\hat o_i - \mathrm{Tr}(O_i\rho)| \le \varepsilon$ for all $i \le M$ simultaneously with probability at least $1 - \delta$. The observables may be chosen after the measurements are performed.

## Proof sketch

Split the $N$ snapshots into $K = O(\log(M/\delta))$ batches, average within each batch, and take medians. Chebyshev's inequality with the shadow-norm variance bound makes each batch mean $\varepsilon$-accurate with probability at least $3/4$, median-of-means amplification brings the failure probability for one observable to $\delta/M$, and a union bound covers all observables.

## Depends on

- [Classical shadows from randomized measurements](randomized-measurement-classical-shadow.md)
- [The shadow norm of an observable](shadow-norm-of-an-observable.md)

## Proof depends on

- [Variance bound for single-snapshot estimators](variance-of-classical-shadow-estimators.md)
- [Median amplification](../../../Probability/concentration-inequalities/median-of-means-amplification/measure-real-sample-median-not-mem-icc-l.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
