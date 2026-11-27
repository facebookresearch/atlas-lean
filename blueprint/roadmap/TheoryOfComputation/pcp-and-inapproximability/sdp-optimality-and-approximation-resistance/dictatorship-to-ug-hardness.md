# Dictatorship tests compose with Unique Games to give hardness

Assume the Unique Games Conjecture. If $\mathrm{GCSP}(\Lambda)$ has a dictatorship test with completeness $c$ and $(\tau, d)$-soundness $s$ for constant $\tau, d$, then for every $\eta > 0$ it is NP-hard to distinguish instances of $\mathrm{GCSP}(\Lambda)$ with $\operatorname{opt} \ge c - \eta$ from instances with $\operatorname{opt} \le s + \eta$.

## Proof sketch

Replace each vertex of a unique game by a long-code table $F_u : [q]^R \to \Delta_q$ and let the verifier pick a random vertex, random neighbours, permute the query points by the constraint permutations and run the dictatorship test. A labelling of value $1 - \varepsilon$ gives dictators passing with probability $c - \eta$. Conversely, a strategy passing with probability above $s + \eta$ has many vertices whose averaged tables have an influential coordinate; decoding a random coordinate among the few influential ones gives a labelling of the unique game of non-negligible value.

## Depends on

- [Dictatorship tests and their completeness and soundness](dictatorship-test.md)
- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)
- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)

## Sources

- S. Khot, G. Kindler, E. Mossel, R. O'Donnell, "Optimal inapproximability results for MAX-CUT and other 2-variable CSPs?", SIAM Journal on Computing 37 (2007) 319-357.
- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
