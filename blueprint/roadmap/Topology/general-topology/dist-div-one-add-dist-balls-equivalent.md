# Bounded metric $d/(1+d)$ is equivalent to $d$

Let $(X, d)$ be a metric space and define

$$
\delta(x, y) = \frac{d(x, y)}{1 + d(x, y)}, \qquad x, y \in X.
$$

Then $\delta$ is a metric on $X$ ($\delta(x, y) = 0$ exactly when $x = y$, $\delta$ is symmetric, and it satisfies the
triangle inequality), and $d$ and $\delta$ are equivalent: for every $x \in X$ and every $\varepsilon > 0$ there is
$\eta > 0$ with $B_d(x, \eta) \subseteq B_\delta(x, \varepsilon)$, and there is $\eta > 0$ with
$B_\delta(x, \eta) \subseteq B_d(x, \varepsilon)$, where $B_d$ and $B_\delta$ denote open balls.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in real analysis), problem `ma_proofbench_l1_65`. The source asks only that $d$-balls and $\delta$-balls be mutually nested; the statement above also includes the claim that $\delta$ is a metric.
