# Dvořák–Kupec–Kazda–Kolmogorov–Rolínek: dichotomy for planar Boolean CSPs

Let $\Gamma$ be a finite Boolean constraint language. If $\Gamma$ satisfies Schaefer's criterion, or every relation of $\Gamma$ is an even delta-matroid, then $\mathrm{PlanarCSP}(\Gamma)$ is solvable in polynomial time; otherwise $\mathrm{PlanarCSP}(\Gamma)$ is NP-complete. Thus planarity changes the complexity of Boolean CSPs exactly for the non-Schaefer languages of even delta-matroids, such as the exactly-one constraints of planar perfect matching.

## Proof sketch

Hardness: without Schaefer polymorphisms, constants or disequality and the 1-in-3 relation are planarly expressible, and a cyclic exchange obstruction yields a crossover gadget, so (non-planar) 1-in-3-SAT reduces to the planar problem. Tractability: Schaefer cases by Schaefer's theorem, the remaining cases by the reduction to edge CSPs over even delta-matroids.

## Depends on

- [Planar Boolean CSP](planar-boolean-csp.md)
- [Schaefer's six tractable classes](../../boolean-constraint-satisfaction/schaefer-dichotomy/schaefers-six-tractable-classes.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)

## Proof depends on

- [Dvořák–Kupec crossover gadgets](dvorak-kupec-crossover-gadgets.md)
- [Planar expressibility of constants and disequality](planar-expressibility-of-constants.md)
- [Planar CSPs over even delta-matroids reduce to edge CSPs](planar-even-delta-matroid-csp-tractable.md)
- [Schaefer's dichotomy theorem](../../boolean-constraint-satisfaction/schaefer-dichotomy/schaefers-dichotomy-theorem.md)

## Sources

- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
