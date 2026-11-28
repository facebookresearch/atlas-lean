# Unique Games is NP-hard with completeness one half

For every $\varepsilon > 0$ there is $R$ such that, given a unique-games instance with label set $[R]$, it is NP-hard to distinguish whether its value is at least $\frac{1}{2} - \varepsilon$ or at most $\varepsilon$. Equivalently, the Unique Games Conjecture holds with completeness $1/2$ in place of $1 - \varepsilon$.

## Proof sketch

Given a $2$-to-$2$ game of value at least $1 - \varepsilon$, replace each $2$-to-$2$ constraint by the unique constraint obtained from choosing a uniformly random perfect matching inside each $K_{2,2}$ block in a coordinated way: a satisfied $2$-to-$2$ constraint stays satisfied with probability $1/2$, so completeness becomes $\frac{1}{2} - \varepsilon$, while any unique-games labeling is also a $2$-to-$2$ labeling, preserving soundness $\varepsilon$.

## Depends on

- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Proof depends on

- [The 2-to-2 Games Theorem (imperfect completeness)](two-to-two-theorem.md)

## Sources

- S. Khot, D. Minzer, M. Safra, "Pseudorandom sets in Grassmann graph have near-perfect expansion", FOCS (2018); Annals of Mathematics 198 (2023), ECCC TR18-006.
- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "Towards a proof of the 2-to-1 games conjecture?", STOC (2018), ECCC TR16-198.
