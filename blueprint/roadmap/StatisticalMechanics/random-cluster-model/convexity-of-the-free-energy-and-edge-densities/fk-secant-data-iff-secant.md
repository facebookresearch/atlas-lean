# The eventual tilt criterion is equivalent to the wired/free secant comparison

Let $d, N \in \mathbb{N}$ and let $e$ be an unordered pair of vertices of $\Lambda_N = \{-N, \dots, N\}^d$, viewed as a pair in $\mathbb{Z}^d$. At $q = 2$, the [abstract eventual tilt criterion](fksecant-data.md) for $e$ holds if and only if the wired and free infinite-volume densities satisfy

$$\theta^1_e(p') \le \theta^0_e(p) \qquad \text{for every } 0 < p' < p < 1.$$

The [forward implication](hsecant-discharged.md) uses the volume-growth argument. For the converse take $S_n = 0$ and $V_n = n + 1$. For each fixed $p' < p$ and $\varepsilon > 0$, the comparison makes $\theta^1_e(p') - \theta^0_e(p) - 2\varepsilon$ strictly negative. Since the tilt factor is in $(0,1)$, its power with this coefficient times $V_n$ tends to infinity. It is therefore eventually at least $\varepsilon^2$, which gives the required tilt inequality. The witnesses do not use any finite-box FK measure.
