# Standard form of a stabilizer code

Let $S$ be a stabilizer group on $n$ qubits with $n - k$ independent generators, and write the generators as the rows
of an $(n - k) \times 2n$ binary matrix $(A \mid B)$, where row $j$ has a $1$ in column $i$ of $A$ when the generator
acts on qubit $i$ by $X$ or $Y$, and in column $i$ of $B$ when it acts by $Z$ or $Y$ (phases dropped). Let $r$ be the
rank of $A$. Replacing generators by products of generators (adding rows) and permuting the qubits (the same
permutation of the columns of $A$ and of $B$) brings the matrix to the form

$$\left(\begin{array}{ccc|ccc} I_r & A_1 & A_2 & B & C_1 & C_2 \\ 0 & 0 & 0 & D & I_{n-k-r} & E \end{array}\right),$$

with column blocks of widths $r$, $n - k - r$, $k$ in each half and row blocks of heights $r$ and $n - k - r$.

Proof: Gaussian elimination on $A$ gives $r$ rows $(I\ A' \mid \cdot)$ and $n - k - r$ rows $(0 \mid D\ E')$; elimination
on $E'$ gives a block $I$ of size equal to its rank and $s$ further rows $(0 \mid D_2\ 0\ 0)$. These last rows must
commute with the first $r$ generators, which by the
[commutation criterion](pauli-operators-commute-iff-symplectic-product-vanishes.md) forces $D_2 = 0$, impossible for
independent generators unless $s = 0$.

## Depends on

- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)
- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- R. Cleve and D. Gottesman, *Efficient computations of encodings for quantum error correction*, Phys. Rev. A 56 (1997), 76–82, arXiv:quant-ph/9607030, Section III (a standard form of the generator matrices by Gaussian elimination and permutation of the qubits, with the column blocks in another order).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 4.1, equations (4.1)–(4.4).
