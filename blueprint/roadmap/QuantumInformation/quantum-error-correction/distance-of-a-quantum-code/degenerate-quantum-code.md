# Degenerate quantum code

Let $Q$ be a quantum code with orthonormal basis $|\bar\imath\rangle$ and let $\mathcal{E} = \{E_a\}$ be a linearly
independent set of errors (for a set that is not, first choose a basis of its span) satisfying the [Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-iff-knill-laflamme.md)
$\langle \bar\imath | E_a^{*} E_b | \bar\jmath \rangle = C_{ab}\, \delta_{ij}$. The code is degenerate for $\mathcal{E}$ when
the Hermitian matrix $(C_{ab})$ is singular, and nondegenerate for $\mathcal{E}$ when it is invertible. For a
nondegenerate code the vectors $E_a |\bar\imath\rangle$ are linearly independent, since their Gram matrix is
$C \otimes I$; in a degenerate code some nonzero combination of errors annihilates every codeword, so distinct errors can
act identically on the code. Linear independence matters: the families $\{I\}$ and $\{I, -I\}$
span the same errors, but the second has a singular matrix $(C_{ab})$ without any nonzero error in the span annihilating
the code.

For a stabilizer code with stabilizer $S$ and distance $d$, Gottesman and Preskill call the code degenerate when $S$
contains an element other than $I$ of weight less than $d$, and nondegenerate otherwise. Whether a code is degenerate
depends on the error set: Shor's nine-qubit code is degenerate, since $Z_1 Z_2$ lies in its stabilizer and $Z_1$, $Z_2$
act identically on the code.

## Depends on

- [The Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-iff-knill-laflamme.md)
- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)

## Background

- [Codewords of Shor's nine-qubit code](../bit-flip-and-shor-codes/shor-codeword.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2 (after equation (30): "If the matrix $C_{ab}$ in (30) has maximum rank, the code is called nondegenerate. If not, as for the nine-qubit code, the code is degenerate") and Section 2.3 (degenerate stabilizer codes).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 2.3 (degenerate code: $C_{ab}$ singular) and Section 3.2 (stabilizer codes).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.1, the end of the section.
