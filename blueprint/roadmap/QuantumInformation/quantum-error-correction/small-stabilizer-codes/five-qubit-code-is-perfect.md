# The five-qubit code is perfect

For the [five-qubit code](five-qubit-code.md), the fifteen single-qubit Pauli errors $X_i, Y_i, Z_i$ ($i = 1, \dots, 5$)
have pairwise distinct nonzero [syndromes](../stabilizer-formalism/error-syndrome.md), so every nonzero syndrome in
$\mathbb{F}_2^4$ is the syndrome of exactly one of these fifteen errors (single-qubit Pauli errors are taken up to phase). Equivalently, the code attains the
[quantum Hamming bound](../bounds-on-quantum-codes/quantum-hamming-bound.md) with equality: $1 + 3 \cdot 5 = 2^{5 - 1}$,
so the $2 \cdot 16 = 32$ vectors $E |\bar x\rangle$, for $E \in \{I\} \cup \{X_i, Y_i, Z_i\}$, form an orthogonal basis of the
whole space of five qubits.

Proof: the syndrome of $X_i$ is the $i$-th column of the $Z$ part of the generator matrix, that of $Z_i$ the $i$-th
column of its $X$ part, and that of $Y_i$ their sum; the fifteen columns are the fifteen nonzero vectors of
$\mathbb{F}_2^4$ (Preskill's tables).

## Depends on

- [The five-qubit code](five-qubit-code.md)
- [Error syndrome of a stabilizer code](../stabilizer-formalism/error-syndrome.md)
- [The quantum Hamming bound](../bounds-on-quantum-codes/quantum-hamming-bound.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)
- [The five-qubit code is a nondegenerate $[[5, 1, 3]]$ code](five-qubit-code-is-a-nondegenerate-5-1-3-code.md)

## Sources

- R. Laflamme, C. Miquel, J. P. Paz and W. H. Zurek, *Perfect quantum error correcting code*, Phys. Rev. Lett. 77 (1996), 198–201, arXiv:quant-ph/9602019 (a five-qubit code whose fifteen single-qubit errors and the identity use all sixteen syndromes).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2 (equation (35): for $t = k = 1$ the quantum Hamming bound gives $n \ge 5$, and a code with $n = 5$ exists) and Section 3.1, Table 4.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.8.1, equation (7.101), and Section 7.10, the syndrome tables.
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.3 ("every possible error syndrome is used by the single-qubit errors. It is therefore a perfect code").
