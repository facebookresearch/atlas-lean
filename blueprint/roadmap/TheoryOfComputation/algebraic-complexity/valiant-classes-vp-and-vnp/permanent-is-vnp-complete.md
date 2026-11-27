# Valiant: the permanent is VNP-complete

Over every field $K$ of characteristic different from $2$, the permanent family $(\mathrm{per}_n)$ is $\mathsf{VNP}$-complete under p-projections; the Hamiltonian cycle family $(\mathrm{HC}_n)$ is $\mathsf{VNP}$-complete over every field. Hence, over a field of characteristic other than $2$, $\mathsf{VP}_K=\mathsf{VNP}_K$ iff the permanent family has polynomial-size arithmetic circuits, and over every field iff the Hamiltonian cycle family does. (In characteristic $2$ the permanent equals the determinant and lies in $\mathsf{VP}$.)

## Proof sketch

Given $f=\sum_e g(x,e)$, take $g$ of polynomial formula size (Valiant's theorem that $\mathsf{VNP}$ is unchanged when the summands are required to have polynomial-size formulas), and build from the formula a weighted digraph whose cycle-cover sum is $g$, with edges labelled by variables, selectors or constants. For each selector $e_i$, add a rosette gadget whose connector edges are glued, by three-vertex glue gadgets with edge weights $\pm\tfrac12$ (this needs characteristic other than $2$), to the edges labelled $e_i$; the cycle covers of the new graph then sum $g$ over all $0/1$ values of the selectors, so $f$ is a projection of a polynomially larger permanent. The Hamiltonian cycle family is handled by a separate gadget construction that needs no division and works over every field.

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
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Theorems 3.5 and 3.7 and Section 3.3.4.
