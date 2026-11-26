# Valiant: the permanent is VNP-complete

Over every field $K$ of characteristic different from $2$, the permanent family $(\mathrm{per}_n)$ is $\mathsf{VNP}$-complete under p-projections; the Hamiltonian cycle family $(\mathrm{HC}_n)$ is $\mathsf{VNP}$-complete over every field. Hence $\mathsf{VP}_K=\mathsf{VNP}_K$ iff the permanent has polynomial-size arithmetic circuits.

## Proof sketch

Given $f=\sum_e g(x,e)$ with $g$ of polynomial formula size (formula-size summands suffice by Valiant's theorem that p-definability with formulas equals p-definability with circuits), write $g$ as a projection of a permanent via its formula, then sum out each Boolean selector by an additional row and column (which needs $2$ invertible), keeping the result a projection of a polynomially larger permanent.

## Depends on

- [Valiant's class VNP (p-definable families)](valiants-class-vnp.md)
- [Projections and p-projections](projections-and-p-projections.md)

## Proof depends on

- [The permanent is in VNP via Ryser's formula](permanent-is-in-vnp.md)
- [The Hamiltonian cycle polynomial is in VNP](hamiltonian-cycle-polynomial-in-vnp.md)
- [Arithmetic formulas are projections of the permanent](../determinantal-and-permanental-complexity/formulas-are-projections-of-permanents.md)
- [VP is contained in VNP, and VNP is closed under p-projections](vp-subset-vnp.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Peter Bürgisser, "Completeness and Reduction in Algebraic Complexity Theory", Springer, 2000.
