# Surface codes on closed surfaces

Let $\Sigma$ be a closed orientable surface of genus $g \ge 1$ with a cellulation (a graph embedded in $\Sigma$ whose faces
are discs). The surface code puts a qubit on each edge, with check operators $A_s = \prod_{j \ni s} X_j$ for vertices and
$B_p = \prod_{j \in \partial p} Z_j$ for faces. It encodes $2g$ qubits, the dimension of the first homology group
$H_1(\Sigma; \mathbb{F}_2)$, and its distance is the least number of edges of a homologically nontrivial cycle of the graph
or of the dual graph. The [toric code](toric-code.md) is the case $g = 1$ with the square lattice. Kitaev phrases the
count as a $4^g$-fold degenerate ground space of the corresponding Hamiltonian.

## Expansion

A good expansion adds pages for the $\mathbb{F}_2$ chain complex of a cellulated surface (faces, edges, vertices with
boundary maps $\partial_2, \partial_1$ and $\partial_1 \partial_2 = 0$), for $\dim H_1(\Sigma; \mathbb{F}_2) = 2g$, and for the
identification of the normalizer modulo the stabilizer with $H_1 \oplus H^1$, generalising the
[toric-code characterisation](logical-operators-of-the-toric-code.md).

## Depends on

- [Toric code](toric-code.md)

## Informally uses

- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)
- [Dimension of a stabilizer code](../finrank-stabilizer-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.B (the paragraph on generalisations: "For a closed orientable Riemann surface of genus $g$, $2g$ qubits can be encoded").
- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 1 ("On a compact orientable surface of genus $g$, the ground state is $4^g$-fold degenerate").
