# NP-hardness of approximating Vertex Cover within sqrt(2) - epsilon

For every $\varepsilon > 0$ it is NP-hard, given a graph $G$ on $N$ vertices, to distinguish whether $G$ has an independent set of size at least $\bigl(1 - \frac{1}{\sqrt{2}} - \varepsilon\bigr)N$ or every independent set of $G$ has size at most $\varepsilon N$. Consequently, it is NP-hard to approximate minimum vertex cover within a factor $\sqrt{2} - \varepsilon$.

## Proof sketch

Apply the $2$-to-$2$ theorem and the standard reduction from label cover to independent set in which each vertex of the game is replaced by a cloud indexed by labels weighted by a $p$-biased measure with $p = 1 - 1/\sqrt{2}$; consistent labelings give large independent sets, and independent sets of non-negligible size in the NO case decode to good labelings via the structure of non-expanding sets in the corresponding Grassmann/biased product graphs. Optimizing $p$ gives the ratio $\sqrt{2}$, improving the Dinur-Safra bound $1.36$.

## Depends on

- [Approximation algorithms and approximation ratios](../../../ComputerScience/approximation-algorithms/approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [The 2-to-2 Games Theorem (imperfect completeness)](two-to-two-theorem.md)

## Sources

- S. Khot, D. Minzer, M. Safra, "On independent sets, 2-to-2 games, and Grassmann graphs", STOC (2017), ECCC TR16-124.
- S. Khot, D. Minzer, M. Safra, "Pseudorandom sets in Grassmann graph have near-perfect expansion", FOCS (2018); Annals of Mathematics 198 (2023), ECCC TR18-006.
- I. Dinur, S. Safra, "On the hardness of approximating minimum vertex cover", Annals of Mathematics 162 (2005) 439-485.
