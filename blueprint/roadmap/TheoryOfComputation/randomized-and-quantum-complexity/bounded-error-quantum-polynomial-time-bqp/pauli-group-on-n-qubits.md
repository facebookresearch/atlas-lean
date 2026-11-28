# The Pauli group on $n$ qubits

The $n$-qubit Pauli group is

$$\mathcal{P}_n = \{\, i^k P_1 \otimes \cdots \otimes P_n : k \in \{0, 1, 2, 3\},\ P_j \in \{I, X, Y, Z\} \,\},$$

a group of $4^{n+1}$ unitaries under multiplication. Every element can be written uniquely as $c\, X^a Z^b$ with
$c \in \{\pm 1, \pm i\}$ and $a, b \in \mathbb{F}_2^n$, where $X^a Z^b$ is the
[Pauli operator](../../../QuantumInformation/quantum-error-correction/css-codes/pauli.md) acting by $X^{a_j} Z^{b_j}$ on
qubit $j$ (so $Y = iXZ$ on the qubits where both $a_j$ and $b_j$ are $1$). In this binary representation

$$X^a Z^b \cdot X^{a'} Z^{b'} = (-1)^{b \cdot a'}\, X^{a + a'} Z^{b + b'} ,$$

so modulo the phases $\{\pm 1, \pm i\}$ the group is the vector space $\mathbb{F}_2^{2n}$, with products becoming sums of
the vectors $(a, b)$. A *tableau* of elements $c_1 X^{a_1} Z^{b_1}, \dots, c_m X^{a_m} Z^{b_m}$ lists the vectors
$(a_j, b_j)$ as the rows of an $m \times 2n$ binary matrix, together with the phases $c_j$. Every element squares to
$\pm I$, and an element is Hermitian exactly when it squares to $I$.

## Depends on

- [Pauli operator $X^a Z^b$ on $n$ qubits](../../../QuantumInformation/quantum-error-correction/css-codes/pauli.md)
- [Unitary evolution and elementary gates](../../../QuantumInformation/quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 20.1 ("$\mathcal{P}_n = \{+1, -1, +i, -i\} \cdot \{I, X, Y, Z\}^{\otimes n}$ ... which has $4^{n+1}$ elements").
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.4 (the binary representation of the Pauli group).
- S. Aaronson and D. Gottesman, *Improved simulation of stabilizer circuits*, Phys. Rev. A 70 (2004), 052328, arXiv:quant-ph/0406196, Section III (the tableau algorithm, whose rows are Hermitian Pauli operators recorded by their $x$ and $z$ bits and one real sign bit, in contrast with a general list of Pauli group elements with fourth-root phases).
