# Raghavendra–Steurer: small-set expansion hypothesis implies the Unique Games Conjecture

The small-set expansion hypothesis implies the Unique Games Conjecture. More precisely, for every $\varepsilon > 0$ there are $\eta, \delta > 0$ and a polynomial-time reduction from $\mathrm{SSE}(\eta, \delta)$ to unique games with value either at least $1 - \varepsilon$ or at most $\varepsilon$. Moreover (Raghavendra–Steurer–Tulsiani), the hypothesis is equivalent to the following strengthening of the Unique Games Conjecture: for every $\varepsilon, \eta > 0$ and $M \in \mathbb{N}$ there are $\delta > 0$ and an alphabet size $q$ such that it is NP-hard to distinguish unique-games instances of value at least $1 - \varepsilon$ from instances of value less than $\eta$ whose constraint graph $G$ moreover satisfies $\Phi_G(S) > 1 - \varepsilon$ for every vertex set $S$ of measure $\mu(S) = |S|/|V(G)|$ with $\delta \le \mu(S) \le M\delta$.

## Proof sketch

Given a graph $G$, build a unique game whose vertices are $R$-tuples of vertices of $G$ and whose constraints are noisy random-walk steps applied coordinatewise, with permutations of the $R$ coordinates as constraints. A non-expanding set $S$ of measure $\delta \approx 1/R$ gives a labelling choosing the coordinate lying in $S$, of value close to $1$. Conversely, a good labelling defines, via an averaging and invariance argument, a set of measure about $1/R$ in $G$ with expansion bounded away from $1$.

## Depends on

- [The small-set expansion hypothesis](small-set-expansion-hypothesis.md)
- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Proof depends on

- [Dictatorship tests compose with Unique Games to give hardness](dictatorship-to-ug-hardness.md)

## Sources

- P. Raghavendra, D. Steurer, "Graph expansion and the unique games conjecture", STOC (2010).
- P. Raghavendra, D. Steurer, M. Tulsiani, "Reductions between expansion problems", CCC (2012), ECCC TR10-172.
