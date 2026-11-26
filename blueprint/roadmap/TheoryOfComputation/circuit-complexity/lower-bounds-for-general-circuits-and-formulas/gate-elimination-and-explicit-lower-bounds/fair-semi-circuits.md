# Fair semi-circuits over the full binary basis

A *fair semi-circuit* over $n$ variables consists of a system of affine equations over $\mathbb{F}_2$ in auxiliary *parameters* together with an acyclic circuit over the full binary basis $B_2$ whose inputs are literals of the parameters (or of affine forms in them). It computes a function on the solutions of the affine system. Fairness requires that the affine part is consistent and that every parameter is either free or determined by the system, so that restricting a parameter or deleting a satisfied constraint again yields a fair semi-circuit computing the corresponding restriction. Every ordinary $B_2$ circuit is a fair semi-circuit with an empty system, and gate elimination steps for affine dispersers act on semi-circuits.

## Depends on

- [The full binary basis B2 and the basis U2](../../circuit-models-and-classes/circuit-models-and-complexity-measures/full-binary-basis-b2-and-u2.md)
- [Affine dispersers](affine-dispersers.md)

## Sources

- Magnus Gausdal Find, Alexander Golovnev, Edward A. Hirsch, Alexander S. Kulikov, "A Better-than-3n Lower Bound for the Circuit Complexity of an Explicit Function", IEEE 57th Annual Symposium on Foundations of Computer Science, 2016.
