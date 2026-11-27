# Kushilevitz-Mansour: membership queries learn functions of small spectral norm and small decision trees

Let $L \ge 1$, $\varepsilon, \delta > 0$, and let $C_L$ be the Boolean functions on $n$ coordinates whose sign representation has spectral norm $\sum_S|\hat f(S)| \le L$. The Kushilevitz-Mansour algorithm with threshold $\theta = \varepsilon/(2L)$ finds the heavy Fourier coefficients by the Goldreich-Levin bucket search: buckets are indexed by $J \subseteq [n]$ and $S \subseteq J$ with weight $\sum_{U : U \cap J = S}\hat f(U)^2$, coordinates are added one at a time, and buckets of estimated weight below $\theta^2/2$ are discarded. From

$$
m \ge \frac{512L^4}{\varepsilon^4}\ln\frac{2(n+2)2^n}{\delta}
$$

samples (each sample is three uniform points, giving $m(2n+3)$ non-adaptive membership queries) it learns $C_L$ with error $\varepsilon$ and confidence $1-\delta$. Since a decision tree with at most $L$ leaves has spectral norm at most $L$, the same bound learns such trees.

## Proof sketch

A set $U$ with $|\hat f(U)| \ge \theta$ contributes $\theta^2$ to every bucket containing it, so with accurate estimates it survives every level; when estimates are within $\theta^2/4$, every surviving bucket weighs more than $\theta^2/4$, and by Parseval at most $4/\theta^2$ survive per level. Bucket weights are expectations of products of $f$ at correlated points, estimable from three-point samples. Rounding the sign of the expansion on the heavy sets has error at most the weight off them, which is at most $\theta L \le \varepsilon/2$ plus estimation error.

## Depends on

- [Randomized membership-query learner as a family of decision trees](membership-query-learner.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)
- [Rounding to the sign](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/bool-dist-le-expect-sq-sub.md)

## Sources

- Eyal Kushilevitz and Yishay Mansour, "Learning Decision Trees Using the Fourier Spectrum", SIAM Journal on Computing, 1993.
- Oded Goldreich and Leonid A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing, 1989.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
