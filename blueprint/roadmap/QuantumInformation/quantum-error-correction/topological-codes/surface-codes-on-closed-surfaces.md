# Surface codes on closed surfaces

Let $\Sigma$ be a closed orientable surface of genus $g \ge 1$ with a cellulation (a graph embedded in $\Sigma$ whose faces
are discs). The surface code puts a qubit on each edge, with check operators $A_s = \prod_j X_j^{(\partial_1)_{s j}}$ for vertices
and $B_p = \prod_j Z_j^{(\partial_2)_{j p}}$ for faces, where $\partial_1$ and $\partial_2$ are the cellular boundary matrices
reduced modulo $2$, so incidences are counted with multiplicity: an edge traversed twice by the boundary of a face, such
as a pendant edge inside the face, does not appear in $B_p$, and a loop at $s$ does not appear in $A_s$. (Taking products
over the sets of incident edges instead would make such a face check anticommute with the vertex check at the leaf.) It encodes $2g$ qubits, the dimension of the first homology group
$H_1(\Sigma; \mathbb{F}_2)$, and its distance is the least number of edges of a homologically nontrivial cycle of the graph
or of the dual graph. The [toric code](toric-code.md) is the case $g = 1$ with the square lattice. Kitaev phrases the
count as a $4^g$-fold degenerate ground space of the corresponding Hamiltonian.

## Expansion

A good expansion adds pages for the $\mathbb{F}_2$ chain complex of a cellulated surface (faces, edges, vertices with
boundary maps $\partial_2, \partial_1$ and $\partial_1 \partial_2 = 0$), for $\dim H_1(\Sigma; \mathbb{F}_2) = 2g$, and for the
identification of $N(S) / (\langle iI \rangle S)$, the normalizer modulo the stabilizer and phases, with $H_1 \oplus H^1$
(the phases must be divided out: $N(S)/S$ still contains $iI$, of order $4$, while $H_1 \oplus H^1$ over $\mathbb{F}_2$ has
exponent $2$), generalising the
[toric-code characterisation](logical-operators-of-the-toric-code.md).

## Depends on

- [Toric code](toric-code.md)

## Informally uses

- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)
- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.B (the paragraph on generalisations: "For a closed orientable Riemann surface of genus $g$, $2g$ qubits can be encoded").
- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 2 of the published article (Section 1 of the arXiv version) ("On a compact orientable surface of genus $g$, the ground state is $4^g$-fold degenerate").
