# Approximation-resistant predicates and balanced pairwise independence

A predicate $P \subseteq [q]^k$ with density $\rho(P) = |P|/q^k$ is **approximation resistant** if for every $\varepsilon > 0$ it is NP-hard (or UG-hard, when stated relative to the Unique Games Conjecture) to distinguish instances of Max-$P$ with value at least $1 - \varepsilon$ from instances with value at most $\rho(P) + \varepsilon$; i.e. no efficient algorithm beats a uniformly random assignment. A distribution $\mu$ on $[q]^k$ is **balanced pairwise independent** if for all $i \ne j$ and $a, b \in [q]$,

$$
\Pr_{x \sim \mu}[x_i = a,\ x_j = b] = \frac{1}{q^2}.
$$

The predicate $P$ **supports** such a distribution if $\operatorname{supp}(\mu) \subseteq P$.

## Depends on

- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)

## Sources

- P. Austrin, E. Mossel, "Approximation resistant predicates from pairwise independence", Computational Complexity 18 (2009) 249-271, arXiv:0802.2300.
- S. O. Chan, "Approximation resistance from pairwise-independent subgroups", Journal of the ACM 63 (2016), STOC (2013), ECCC TR12-110.
- J. Håstad, "Some optimal inapproximability results", Journal of the ACM 48 (2001) 798-859.
