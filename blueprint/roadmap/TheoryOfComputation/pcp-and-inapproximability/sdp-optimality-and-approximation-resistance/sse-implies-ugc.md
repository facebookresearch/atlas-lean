# Raghavendra–Steurer: small-set expansion hypothesis implies the Unique Games Conjecture

The small-set expansion hypothesis implies the Unique Games Conjecture. More precisely, for every $\varepsilon > 0$ there are $\eta, \delta > 0$ and a polynomial-time reduction from $\mathrm{SSE}(\eta, \delta)$ to unique games with value either at least $1 - \varepsilon$ or at most $\varepsilon$, and the unique-games instances produced are themselves small-set expanders in the NO case; hence the hypothesis also implies Unique Games hardness on instances whose constraint graphs are small-set expanders.

## Proof sketch

Given a graph $G$, build a unique game whose vertices are $R$-tuples of vertices of $G$ and whose constraints are noisy random-walk steps applied coordinatewise, with permutations of the $R$ coordinates as constraints. A non-expanding set $S$ of measure $\delta \approx 1/R$ gives a labelling choosing the coordinate lying in $S$, of value close to $1$. Conversely, a good labelling defines, via an averaging and invariance argument, a set of measure about $1/R$ in $G$ with expansion bounded away from $1$.

## Depends on

- [The small-set expansion hypothesis](small-set-expansion-hypothesis.md)
- [Dictatorship tests compose with Unique Games to give hardness](dictatorship-to-ug-hardness.md)

## Proof depends on

- [The small-set expansion hypothesis](small-set-expansion-hypothesis.md)
- [Dictatorship tests compose with Unique Games to give hardness](dictatorship-to-ug-hardness.md)

## Sources

- P. Raghavendra, D. Steurer, "Graph expansion and the unique games conjecture", STOC (2010).
