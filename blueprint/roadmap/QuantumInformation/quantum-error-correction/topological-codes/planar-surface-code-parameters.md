# Parameters of the planar surface code

For $L \ge 2$ the [planar surface code](planar-surface-code.md) is an $[[L^2 + (L - 1)^2, 1, L]]$ code: its
$2L(L - 1)$ check operators commute and are independent, so it encodes
$L^2 + (L - 1)^2 - 2L(L - 1) = 1$ qubit, and its distance is $L$, the number of edges on a shortest path from one rough
boundary to the other and on a shortest dual path from one smooth boundary to the other.

Proof: a vertex operator and a face operator share $0$ or $2$ edges. Unlike on the torus there is no relation among the
check operators, because every product of vertex operators over a nonempty set acts on some edge an odd number of times
(the dangling edges and the smooth sides), and dually for faces. Logical operators correspond to relative cycles joining
the two rough (respectively smooth) boundaries, and the stabilizer distance criterion gives distance $L$.

## Depends on

- [Planar surface code](planar-surface-code.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)
- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md)
- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.B ("The lattice has $L^2 + (L-1)^2$ links, $L(L-1)$ plaquettes, and $L(L-1)$ sites ... the number of encoded qubits is $L^2 + (L-1)^2 - 2L(L-1) = 1$").
- S. B. Bravyi and A. Yu. Kitaev, *Quantum codes on a lattice with boundary*, arXiv:quant-ph/9811052 (1998), Abstract.
