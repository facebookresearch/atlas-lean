# Kazda–Kolmogorov–Rolínek: edge CSPs with even delta-matroid constraints are polynomial-time solvable

If every relation of a finite Boolean constraint language $\Gamma$ is an even delta-matroid, then satisfiability of edge instances of $\mathrm{CSP}(\Gamma)$ is decidable in polynomial time. The algorithm maintains a local labeling and repeatedly reduces its number of defects by an augmenting walk between two defects; an improving labeling always yields such a walk, and blossoms (odd cycles of constraints) are contracted into a single even delta-matroid constraint as in Edmonds' matching algorithm.

## Proof sketch

Even delta-matroid exchange shows that if a labeling with fewer defects exists, then the symmetric difference decomposes into trails, one of which is an augmenting walk that can be found by a timestamped search; contraction of blossoms preserves even delta-matroids, so the search recurses on a smaller instance.

## Depends on

- [Edge CSPs and their labeling walks](edge-csps.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Local contraction preserves even delta-matroids](local-contraction-preserves-even-delta-matroids.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
