# Planar expressibility of constants and disequality

Let $\Gamma$ be a finite Boolean language without Schaefer polymorphisms. Then using only planar operations on relations (adjacent identification followed by deletion of one port, projection of a port, pinning a port to a constant, and intersection of two adjacent relations), one can construct from $\Gamma$ either the disequality relation or both constant pins, and when some relation of $\Gamma$ is not self-complementary one obtains a planar pp-definition of the 1-in-3 relation via the triangle of NAND constraints over a ternary relation containing all unit tuples and missing $000$.

## Proof sketch

Each of the six failed Schaefer polymorphisms has a witnessing relation; minors of these relations under the planar operations produce the required binary and ternary relations, and the finite constructions are verified by truth tables.

## Depends on

- [Planar Boolean CSP](planar-boolean-csp.md)
- [Schaefer's six tractable classes](../../boolean-constraint-satisfaction/schaefer-dichotomy/schaefers-six-tractable-classes.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)

## Proof depends on

- [Without Schaefer polymorphisms, all polymorphisms are projections or negated projections](../../boolean-constraint-satisfaction/schaefer-dichotomy/without-schaefer-polymorphisms.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Theorem 15(1) (restating the Dvořák–Kupec hardness result).

- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
