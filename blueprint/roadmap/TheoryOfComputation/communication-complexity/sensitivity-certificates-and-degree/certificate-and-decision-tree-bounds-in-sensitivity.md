# Polynomial bounds in terms of sensitivity: C ≤ 2s⁵ and D ≤ 2s⁶

For every total Boolean function $f$:

$$bs(f) \le 2\, s(f)^4, \qquad C(f) \le 2\, s(f)^5, \qquad D(f) \le 2\, s(f)^6.$$

## Proof sketch

Huang's theorem gives $\deg(f) \le s(f)^2$; with Nisan–Szegedy $bs \le 2\deg^2$ this gives $bs \le 2s^4$; Nisan's $C \le s \cdot bs$ gives $C \le 2s^5$; Midrijanis's $D \le 2\deg^3$ gives $D \le 2 s^6$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Huang's sensitivity theorem](../query-and-communication-measures/huang-s-sensitivity-theorem.md)
- [Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree](nisan-szegedy-bounds.md)
- [Midrijanis: D(f) ≤ deg(f)·bs(f) ≤ 2 deg(f)³](midrijanis-degree-bound.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
- G. Midrijanis, "Exact Quantum Query Complexity for Total Boolean Functions", arXiv:quant-ph/0403168, 2004.
