# Edge CSPs and their labeling walks

An instance of a Boolean CSP is an *edge instance* if every variable occurs in exactly two argument positions (counted with multiplicity). An edge instance is equivalently a multigraph whose vertices are the constraints and whose edges are the variables. A *local labeling* assigns a Boolean value to every argument occurrence so that each constraint's local tuple lies in its relation; its *defects* are the variables whose two occurrences receive different values. The instance is satisfiable iff some local labeling has no defects. An *alternating walk* flips occurrences along a trail of the multigraph, changing defects only at its ends.

## Depends on

- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)
- [Finite-domain constraint satisfaction problems](../constraint-satisfaction-encodings/finite-domain-constraint-satisfaction.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
