# Grid sums are affine projections of the permanent and of the Hamiltonian cycle polynomial

A *grid sum* sums over two families of bits $x\in\{0,1\}^V$ and $r\in\{0,1\}^{W}$ a product of weights, one for each incidence $\nu\in N$ between a bit $x_{v(\nu)}$ and a bit $r_{w(\nu)}$: $\sum_x\sum_r\prod_{\nu\in N}W_\nu\bigl(x_{v(\nu)},r_{w(\nu)}\bigr)$. If, for each bit $r_b$, the weights at the incidences of $r_b$ are affine in one common variable, then the grid sum is an affine projection of $\mathrm{per}_S$ for every $S\ge 3|N|$ when $2\neq0$ in $K$, and of $\mathrm{HC}_S$ for every $S\ge c|N|$ for a constant $c$, over every commutative ring.

## Proof sketch

Build a weighted graph in which each bit is a gadget with two routes (value $0$ or $1$) and each incidence is a small gadget whose cycle covers contribute the corresponding weight; cycle covers (for the permanent) or Hamiltonian cycles of the resulting graph correspond bijectively to assignments.

## Depends on

- [Valiant's class VNP (p-definable families)](valiants-class-vnp.md)
- [Clause sums](clause-sums.md)
- [Projections and p-projections](projections-and-p-projections.md)

## Proof depends on

- [The permanent is in VNP via Ryser's formula](permanent-is-in-vnp.md)

## Sources

- Anthropic, "VP ≠ VNP over every field", manuscript, 2026.
- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
