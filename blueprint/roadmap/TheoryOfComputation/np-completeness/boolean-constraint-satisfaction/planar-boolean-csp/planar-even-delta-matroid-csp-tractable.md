# Dvořák–Kupec: planar CSPs with even delta-matroid cyclic differences reduce to edge CSPs

Let $\Gamma$ be a finite Boolean language in which every relation $R$ is self-complementary and has an even delta-matroid as cyclic difference $dR$. Then $\mathrm{PlanarCSP}(\Gamma)$ reduces in polynomial time to the edge CSP over $d\Gamma \cup \{\mathrm{EVEN}_1, \mathrm{EVEN}_2, \mathrm{EVEN}_3\}$, where $\mathrm{EVEN}_i$ is the set of $i$-tuples of even weight, and is therefore decidable in polynomial time. Without self-complementarity the conclusion fails: planar 1-in-3-SAT, over the even delta-matroid of exactly-one tuples, is NP-complete.

## Proof sketch

In a plane embedding of a planar instance, take as new variables the differences $t_u \oplus t_v$ of the original values along the edges of the face cycles. Every such edge lies on two faces, so each new variable occurs in exactly two constraints: the constraint face with tuple $T$ sees exactly the cyclic difference $dT$, and around each original variable the differences must sum to $0$, a parity constraint that is split into a chain of parity constraints of arity at most $3$. Self-complementarity is what makes the constraints expressible through differences alone, since a solution is recovered from the differences only up to flipping all values. The parity relations are even delta-matroids, so the edge-CSP algorithm applies.

## Depends on

- [Planar Boolean CSP](planar-boolean-csp.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)
- [Edge CSPs, occurrence labelings and defects](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edge-csps-over-even-delta-matroids/edge-csps-and-defects.md)

## Proof depends on

- [Kazda–Kolmogorov–Rolínek: edge CSPs with even delta-matroid constraints are polynomial-time solvable](kazda-kolmogorov-rolinek-edge-csp.md)

## Sources

- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Theorems 8, 15 and 16.
- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998 (NP-completeness of planar positive 1-in-3-SAT).
