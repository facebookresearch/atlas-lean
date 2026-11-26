# Clause sums

A *weighted clause* is a list of literals over Boolean variables together with a weight $w$ (a polynomial); its *contribution* at an assignment is $w$ if all its literals hold and $1$ otherwise. A *clause sum* over Boolean variables $b_1,\dots,b_m$ is $\sum_{b\in\{0,1\}^m}\prod_{C}\mathrm{contr}_C(b)$, a sum over all assignments of the product of the contributions of a family of weighted clauses. Clause sums with polynomially many clauses of bounded width and affine weights are $\mathsf{VNP}$ families.

## Depends on

- [Valiant's class VNP (p-definable families)](valiants-class-vnp.md)

## Sources

- Anthropic, "VP ≠ VNP over every field", manuscript, 2026.
