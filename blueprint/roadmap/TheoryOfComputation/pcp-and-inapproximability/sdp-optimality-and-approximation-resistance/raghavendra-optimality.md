# Raghavendra's theorem: the basic SDP is UGC-optimal for every CSP

Assume the Unique Games Conjecture. For every finite payoff family $\Lambda$, every $c \in [0,1]$ and every $\eta > 0$, it is NP-hard, given an instance $\Im$ of $\mathrm{GCSP}(\Lambda)$ with $\operatorname{opt}(\Im) \ge c - \eta$, to find an assignment of value greater than $S_\Lambda(c) + \eta$. In particular, the best approximation ratio achievable in polynomial time for Max-$P$ equals the integrality gap of the basic SDP, for every predicate $P$.

## Proof sketch

Take a near-optimal $(c, S_\Lambda(c) + \eta/3)$-integrality gap instance, turn it into a dictatorship test via the invariance principle, and compose with Unique Games.

## Depends on

- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)
- [The integrality gap curve of the basic SDP](integrality-gap-curve.md)
- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Proof depends on

- [From SDP integrality gaps to dictatorship tests](gap-instance-to-dictatorship.md)
- [Dictatorship tests compose with Unique Games to give hardness](dictatorship-to-ug-hardness.md)

## Sources

- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
