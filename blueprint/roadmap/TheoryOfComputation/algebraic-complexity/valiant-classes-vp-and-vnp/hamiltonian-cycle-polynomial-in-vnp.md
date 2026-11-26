# The Hamiltonian cycle polynomial is in VNP

The Hamiltonian cycle polynomial $\mathrm{HC}_n(x)=\sum_{\sigma}\prod_{i=1}^n x_{i\sigma(i)}$, the sum over the permutations $\sigma$ of $\{1,\dots,n\}$ consisting of a single $n$-cycle, belongs to $\mathsf{VNP}_K$ over every commutative ring $K$.

## Proof sketch

Encode a cycle by the order in which it visits the vertices starting from vertex $1$: bits $b_{t,u}$ meaning 'position $t$ holds $u$'. A product of local tests ($1-b\,b'$ for pairs of bits in one position or one vertex, and $\sum_ub_{t,u}$ for each position) is $1$ exactly on bit tables of bijections and $0$ otherwise; multiplying by the weights of consecutive positions gives a polynomial-size summand.

## Depends on

- [Valiant's class VNP (p-definable families)](valiants-class-vnp.md)

## Proof depends on

- [VP is contained in VNP, and VNP is closed under p-projections](vp-subset-vnp.md)

## Sources

- Peter Bürgisser, "Completeness and Reduction in Algebraic Complexity Theory", Springer, 2000.
- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
