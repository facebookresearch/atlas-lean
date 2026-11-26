# Error syndrome of a stabilizer code

Let $S$ be a stabilizer group on $n$ qubits with independent generators $M_1, \dots, M_r$ ($r = n - k$). For a Pauli
operator $E \in \mathcal{P}_n$ and each $j$, let $f_j(E) = 0$ if $E$ commutes with $M_j$ and $f_j(E) = 1$ if it
anticommutes. The error syndrome of $E$ is the vector

$$f(E) = (f_1(E), \dots, f_r(E)) \in \mathbb{F}_2^r .$$

If $E = c\, X^a Z^b$ and $M_j = c_j X^{a_j} Z^{b_j}$, then $f_j(E) = \omega((a, b), (a_j, b_j))$ is the
[symplectic product](symplectic-product-of-pauli-operators.md). For a code state $|\psi\rangle$ (with
$M_j |\psi\rangle = |\psi\rangle$ for all $j$) one has $M_j E |\psi\rangle = (-1)^{f_j(E)} E |\psi\rangle$, so measuring
the generators on the corrupted state returns the outcomes $(-1)^{f_j(E)}$ with certainty; this is how the syndrome is
read out in error correction.

## Depends on

- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)
- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)
- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.3 (measuring the generators of $S$ gives a list of eigenvalues, the error syndrome; the syndromes of $E$ and $F$ agree exactly when that of $E^{\dagger} F$ is trivial).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.2, equation (3.9).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.1, equation (7.123), and Section 7.9.2, equation (7.135).
