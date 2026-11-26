# Abboud–Bringmann–Fischer: optimal short cycle removal and near-tight distance-oracle and 4-cycle listing bounds from 3SUM

Assume the 3SUM hypothesis. (i) Listing all triangles in an $n^{1/2}$-regular $n$-vertex graph requires $n^{2-o(1)}$ time even when the number of $k$-cycles is $O(n^{k/2+\gamma})$ with the optimal $\gamma=0$ (previously $\gamma\ge 1/4$). (ii) For approximate distance oracles with stretch $2k\pm O(1)$ and query time $n^{o(1)}$, preprocessing requires $\Omega(m^{1+1/(2k)})$ time, within a factor 2 in the exponent of Thorup–Zwick's $O(mn^{1/k})$; tight bounds also follow for stretch $2+o(1)$ and $3-\varepsilon$. (iii) Listing all $t$ 4-cycles of a graph takes $(\min(m^{4/3},n^2)+t)^{1-o(1)}$ time, so the known $\widetilde{O}(\min(m^{4/3},n^2)+t)$ algorithm is tight up to $n^{o(1)}$ factors.

## Proof sketch

The structure-versus-randomness argument is applied to the numbers of the 3SUM instance rather than to graphs. Using the Balog–Szemerédi–Gowers theorem and Ruzsa's covering lemma, either the instance has a part with small doubling, where a new subquadratic 3SUM algorithm for sets of small doubling applies, or it is additively unstructured, in which case the standard 3SUM-to-triangle-listing reduction produces graphs with essentially the random number of short cycles.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Proof depends on

- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Sources

- Amir Abboud, Karl Bringmann and Nick Fischer, "Stronger 3-SUM Lower Bounds for Approximate Distance Oracles via Additive Combinatorics", STOC (2023), arXiv:2211.07058.
- Amir Abboud, Karl Bringmann, Seri Khoury and Or Zamir, "Hardness of Approximation in P via Short Cycle Removal: Cycle Detection, Distance Oracles, and Beyond", STOC (2022), arXiv:2204.10465.
