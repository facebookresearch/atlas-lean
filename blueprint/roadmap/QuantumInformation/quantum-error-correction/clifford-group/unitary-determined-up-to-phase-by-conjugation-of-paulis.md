# A unitary is determined up to phase by its conjugation action on Pauli operators

Let $U, V$ be unitary $2^n \times 2^n$ matrices with $U P U^{*} = V P V^{*}$ for every Pauli operator
$P = X^a Z^b$, $a, b \in \mathbb{F}_2^n$. Then $U = e^{i\theta} V$ for some $\theta \in \mathbb{R}$. In particular an
element of the Clifford group is determined, up to a global phase, by the images of $X_j$ and $Z_j$
($j = 1, \dots, n$), and the unitaries acting trivially on the Pauli group by conjugation are exactly the scalars
$e^{i\theta} I$.

Proof: $W = V^{*} U$ commutes with every $X^a Z^b$. These $4^n$ operators form a basis of the $2^n \times 2^n$ complex
matrices, so $W$ commutes with every matrix and is a scalar; being unitary, $W = e^{i\theta} I$.

## Depends on

- [Pauli operator $X^a Z^b$ on $n$ qubits](../css-codes/pauli.md)
- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)

## Proof depends on

- [Every matrix is a combination of Pauli operators](../stabilizer-formalism/pauli-expansion-of-a-matrix.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.5 ("to specify a Clifford group operator $U$, it is sufficient to indicate its action on a generating set for the Pauli group").
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2, equation (7.12) (expansion of operators in Pauli operators).
