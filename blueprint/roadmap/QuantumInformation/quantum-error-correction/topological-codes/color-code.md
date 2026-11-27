# Color code

Take a lattice embedded in a closed surface such that three edges meet at every vertex and the faces (plaquettes) can be
coloured with three colours so that adjacent faces have different colours. Put a qubit on each vertex. The *color code* is
the stabilizer code whose stabilizer is generated, for every plaquette $p$, by
$B_p^X = \prod_{i \in p} X_i$ and $B_p^Z = \prod_{i \in p} Z_i$, the products over the vertices of $p$. The generators
commute because two plaquettes share an even number of vertices, and the code encodes $k = 4 - 2\chi$ qubits, where $\chi$
is the Euler characteristic of the surface, so $k$ depends only on the surface. Each generator acts on the qubits of one plaquette, so its weight is the size of that plaquette; the weights are
uniformly bounded for families of lattices with bounded face size (trivalence alone does not bound them: a prism over
an even $m$-gon is trivalent and face-three-colourable, and its base checks have weight $m$). A *triangular code* is a color code on a planar region with three boundaries, one of each colour, obtained by
removing a vertex from a lattice on the sphere; it encodes one qubit, with logical operators $\bar X = X^{\otimes n}$ and
$\bar Z = Z^{\otimes n}$ (the number $n$ of qubits is odd).

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Sources

- H. Bombin and M. A. Martin-Delgado, *Topological quantum distillation*, Phys. Rev. Lett. 97 (2006), 180501, arXiv:quant-ph/0605138, equations (1)–(3), Figures 1–4 and the construction of triangular codes.
