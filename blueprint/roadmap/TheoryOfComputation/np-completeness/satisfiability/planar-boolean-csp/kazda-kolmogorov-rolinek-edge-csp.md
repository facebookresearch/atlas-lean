# Kazda–Kolmogorov–Rolínek: edge CSPs with even delta-matroid constraints are polynomial-time solvable

If every relation of a finite Boolean constraint language $\Gamma$ is an even delta-matroid, then satisfiability of edge instances of $\mathrm{CSP}(\Gamma)$ is decidable in polynomial time.

## Proof sketch

An instance with an empty constraint is unsatisfiable. Otherwise every constraint is a nonempty even delta-matroid, so the blossom algorithm returns a valid labeling with the minimum number of defects after at most one more improvement step than there are variables; each step is a forest search with polynomially many nested blossom contractions, so the whole run takes polynomial time. The instance is satisfiable if and only if the returned labeling has no defects.

## Depends on

- [Edge CSPs, occurrence labelings and defects](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edge-csps-over-even-delta-matroids/edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Edge CSPs over even delta-matroids are solvable by a blossom algorithm](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edge-csps-over-even-delta-matroids/edge-csp-blossom-algorithm.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
