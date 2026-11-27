# Polynomial bounds in terms of sensitivity: bs ≤ 2s⁴ and C ≤ 2s⁵

For every total Boolean function $f$:

$$bs(f) \le 2\, s(f)^4, \qquad C(f) \le 2\, s(f)^5.$$

The first bound is already stated on [Huang's sensitivity theorem](../query-and-communication-measures/huang-s-sensitivity-theorem.md); the new consequence recorded here is the bound on certificate complexity.

## Proof sketch

Huang's theorem gives $\deg(f) \le s(f)^2$; with Nisan–Szegedy $bs \le 2\deg^2$ this gives $bs \le 2s^4$; Nisan's $C \le s \cdot bs$ gives $C \le 2s^5$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Huang's sensitivity theorem](../query-and-communication-measures/huang-s-sensitivity-theorem.md)
- [Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree](nisan-szegedy-bounds.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
