# Logical operators of the toric code

For the [toric code](toric-code.md) identify $a, b \in \mathbb{F}_2^{E}$, $E$ the set of edges, with sets of edges. A
Pauli operator $X^a Z^b$ commutes with every check operator if and only if

1. $b$ is a cycle of the lattice: every vertex meets an even number of edges of $b$; and
2. $a$ is a cycle of the dual lattice: every face contains an even number of edges of $a$ (the dual edges of $a$ form a
   cycle on the dual lattice).

It lies in the stabilizer group up to a phase if and only if moreover $b$ is the boundary of a set of faces and $a$ is
the coboundary of a set of vertices (the set of edges with exactly one endpoint in it), that is, both cycles are
homologically trivial. The operators $\bar Z_1, \bar Z_2$, products of $Z$ along a horizontal and a vertical
non-contractible loop of the lattice, and $\bar X_1, \bar X_2$, products of $X$ on the edges crossed by a vertical and a
horizontal non-contractible loop of the dual lattice, satisfy the commutation relations of the Pauli operators of two
qubits and represent the logical operators.

Proof: $Z^b$ anticommutes with $A_s$ exactly when $|b \cap \mathrm{star}(s)|$ is odd, and $X^a$ with $B_p$ exactly when
$|a \cap \partial p|$ is odd; products of the $B_p$ are $Z$'s on boundaries of sets of faces and products of the $A_s$ are
$X$'s on coboundaries of sets of vertices.

## Depends on

- [Toric code](toric-code.md)
- [The normalizer of a stabilizer group is its centralizer](../stabilizer-formalism/normalizer-of-a-stabilizer-group-equals-its-centralizer.md)
- [Logical Pauli operators of a stabilizer code](../stabilizer-formalism/logical-pauli-operators-of-a-stabilizer-code.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)
- [The toric code check operators commute](toric-code-check-operators-commute.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.A and Figure 3.
- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 2 of the published article (Section 1 of the arXiv version) and Figure 2.
