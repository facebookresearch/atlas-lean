# Jin–Xu: tight 3SUM-based lower bound for 4-cycle enumeration

Assume the 3SUM hypothesis. Then All-Edges Sparse Triangle on $n$-vertex graphs with maximum degree $\sqrt n$ and at most $n^{k/2}$ $k$-cycles for every $k\ge 3$ requires $n^{2-o(1)}$ time. Consequently, for every $\varepsilon > 0$ there is no algorithm for **4-Cycle Enumeration** on $n$-vertex $m$-edge graphs that lists all 4-cycles with $n^{o(1)}$ delay after $O(n^{2-\varepsilon})$ or $O(m^{4/3-\varepsilon})$ preprocessing time; a matching upper bound follows by modifying known 4-cycle detection algorithms. The same structural result strengthens the lower bounds of Abboud, Bringmann, Khoury and Zamir for offline approximate distance oracles and approximate dynamic shortest paths.

## Proof sketch

Plug the Sidon-set hardness into the Abboud–Bringmann–Khoury–Zamir reduction from 3SUM to triangle listing: the absence of additive quadruples in the 3SUM instance translates into the absence of excess short cycles in the constructed graph ("short cycle removal" with optimal parameter). A 4-cycle enumerator with small delay applied to a modified graph then lists the triangles of the sparse instance.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Proof depends on

- [Jin–Xu: 3SUM remains n^{2-o(1)}-hard on Sidon sets](jin-xu-3sum-hard-on-sidon-sets.md)

## Sources

- Ce Jin and Yinzhan Xu, "Removing Additive Structure in 3SUM-Based Reductions", STOC (2023), arXiv:2211.07048.
- Amir Abboud, Karl Bringmann, Seri Khoury and Or Zamir, "Hardness of Approximation in P via Short Cycle Removal: Cycle Detection, Distance Oracles, and Beyond", STOC (2022), arXiv:2204.10465.
