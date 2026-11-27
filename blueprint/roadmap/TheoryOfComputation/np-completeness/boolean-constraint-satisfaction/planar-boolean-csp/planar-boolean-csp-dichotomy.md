# Dvořák–Kupec–Kazda–Kolmogorov–Rolínek: dichotomy for planar Boolean CSPs

Let $\Gamma$ be a finite Boolean constraint language. If $\Gamma$ satisfies Schaefer's criterion, or every relation $R$ of $\Gamma$ is self-complementary and its cyclic difference $dR$ is an even delta-matroid, then $\mathrm{PlanarCSP}(\Gamma)$ is solvable in polynomial time; otherwise $\mathrm{PlanarCSP}(\Gamma)$ is NP-complete. Thus planarity lowers the complexity exactly for the non-Schaefer self-complementary languages with even delta-matroid differences, such as planar not-all-equal 3-SAT. Languages of even delta-matroids that are not self-complementary, such as the exactly-one relation, stay NP-complete in the planar setting.

## Proof sketch

Hardness (Dvořák–Kupec): if CSP$(\Gamma)$ is NP-hard and some relation is not self-complementary, constants and the 1-in-3 relation are planarly expressible; if all relations are self-complementary and some $dR$ is not an even delta-matroid, a crossover gadget makes every instance planar. Tractability: Schaefer cases by Schaefer's theorem; in the remaining case Dvořák and Kupec reduce $\mathrm{PlanarCSP}(\Gamma)$ to the edge CSP over $d\Gamma$ and the parity relations of arity at most $3$, all even delta-matroids, which Kazda, Kolmogorov and Rolínek solve in polynomial time (their Theorems 15, 16 and 8).

## Depends on

- [Planar Boolean CSP](planar-boolean-csp.md)
- [Schaefer's six tractable classes](../../boolean-constraint-satisfaction/schaefer-dichotomy/schaefers-six-tractable-classes.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)

## Proof depends on

- [Dvořák–Kupec crossover gadgets](dvorak-kupec-crossover-gadgets.md)
- [Planar expressibility of constants and disequality](planar-expressibility-of-constants.md)
- [Dvořák–Kupec: planar CSPs with even delta-matroid cyclic differences reduce to edge CSPs](planar-even-delta-matroid-csp-tractable.md)
- [Schaefer's dichotomy theorem](../../boolean-constraint-satisfaction/schaefer-dichotomy/schaefers-dichotomy-theorem.md)

## Sources

- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Theorems 15 and 16.
- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998 (NP-completeness of planar positive 1-in-3-SAT).
