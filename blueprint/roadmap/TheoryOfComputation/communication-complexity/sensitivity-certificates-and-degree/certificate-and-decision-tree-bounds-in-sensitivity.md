# Certificate complexity is polynomially bounded by sensitivity

For every total Boolean function $f$, certificate complexity is at most polynomial in sensitivity:

$$C(f) \le s(f)^{5+o(1)},$$

where the $o(1)$ term in the exponent tends to $0$ as $s(f)$ grows.

## Proof sketch

Nisan's inequality gives $C(f) \le s(f)\, bs(f)$, and Huang's theorem bounds block sensitivity by a polynomial in sensitivity. Derived here with explicit constants: Huang's theorem gives $\deg(f) \le s(f)^2$; with Nisan–Szegedy $bs \le 2\deg^2$ this gives $bs \le 2s^4$, and then $C \le s \cdot bs \le 2s^5$. With Tal's sharper $bs \le \deg^2$, which Huang combines into $bs(f) \le s(f)^4$, the same chain gives $C(f) \le s(f)^5$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Huang's sensitivity theorem](../query-and-communication-measures/huang-s-sensitivity-theorem.md)
- [Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree](nisan-szegedy-bounds.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", STOC 2021 (Section 1.1, Table 1, row $C$, column $s$, and the list of inequalities including $C(f) \le bs(f)\, s(f)$).
- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
