# Dissipation bounds all steady-state current fluctuations

Let $X$ be an ergodic continuous-time Markov jump process on a finite state space with rates $r(y, z)$ such that $r(z, y) > 0$ whenever $r(y, z) > 0$, with stationary law $\pi$. On each edge $\{y, z\}$ with positive rates write $j^\pi(y, z) = \pi(y) r(y,z) - \pi(z) r(z,y)$ for the mean current, $F(y, z) = \ln\frac{\pi(y) r(y,z)}{\pi(z) r(z,y)}$ for the force and $\sigma^\pi(y, z) = j^\pi(y, z) F(y, z) \ge 0$ for the entropy production rate (local detailed balance identifies $F$ with a thermodynamic force). The empirical currents $J_T(y,z)/T$ satisfy a large deviation principle with rate function $I$, and $I(j) = \infty$ unless $j$ is conservative, $\sum_z j(y, z) = 0$ at every state $y$. Gingrich, Horowitz, Perunov and England (2016, Eq. (3)) prove that for every conservative $j$

$$I(j) \le \sum_{y<z} \frac{(j(y,z) - j^\pi(y,z))^2\, \sigma^\pi(y,z)}{4\, j^\pi(y,z)^2},$$

the sum running over edges with positive rates, where on an edge with $j^\pi(y,z) = 0$ the factor $\sigma^\pi/(4 (j^\pi)^2)$ is read as its limit $1/(4a)$ with $a = \pi(y) r(y,z) = \pi(z) r(z,y)$. For a generalized current $J_d = \sum_{y<z} d(y,z) J_T(y,z)$ with nonzero mean rate $j_d^\pi$ and total entropy production rate $\Sigma^\pi = \sum_{y<z} \sigma^\pi(y,z)$, they obtain (Eq. (4)) $I(j_d) \le (j_d - j_d^\pi)^2\, \Sigma^\pi / (4 (j_d^\pi)^2)$; with the scaled variance $V_d = \lim_{T\to\infty} \mathrm{Var}(J_d(T))/T$, this gives the thermodynamic uncertainty relation $V_d\, \Sigma^\pi \ge 2 (j_d^\pi)^2$ (Eq. (8); units $k_B = 1$).

## Depends on

- [Large deviation principle for a sequence of measures](../../../Probability/large-deviations/large-deviation-principle/satisfies-ldp.md)
- [Rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md)
- [Path of a continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Expansion

1. The model: [finite continuous-time Markov chains](../../../Probability/markov-chains/finite-continuous-time-markov-chains/README.md) as path processes ([path-process construction](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/README.md)), the reversibility of the transition graph, the stationary law, edge currents, forces and entropy production.
2. The large deviation principle for the empirical currents (the level-2.5 principle for empirical measure and currents, and its contraction), with the conservation constraint; this is a prerequisite to be stated and proved on its own, not supplied by the general [large deviation bounds](../../../Probability/large-deviations/large-deviation-principle/borel-bounds.md), which assume a principle.
3. The edge-wise quadratic bound, including the convention on edges with zero mean current.
4. The bound for generalized currents with nonzero mean.
5. The uncertainty relation for the scaled variance $V_d$, with the differentiability of the rate function at its minimum (or the scaled-cumulant route) stated as a hypothesis; the unscaled variance of $J_d(T)/T$ tends to $0$ and does not satisfy the bound.

## Sources

- T. R. Gingrich, J. M. Horowitz, N. Perunov and J. L. England, Dissipation bounds all steady-state current fluctuations, Phys. Rev. Lett. 116 (2016), 120601, Eqs. (3), (4) and (8). <https://arxiv.org/abs/1512.02212>
