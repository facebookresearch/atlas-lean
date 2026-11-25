# Correctable errors form a linear space

If the errors $A_a$ are [correctable](is-correctable.md) on a code, then so is every family
$B_b$ of linear combinations of the $A_a$, and the same recovery channel works. This is the last
assertion of Knill and Laflamme's Theorem 3.1 ("the family $\mathcal{A}(C, \mathcal{R})$ is
linearly closed"). No hypothesis on $P$ is needed: if $R_r A_a P = \lambda_{ra} P$ for all $a$,
then $R_r \big(\sum_a \mu_a A_a\big) P = \big(\sum_a \mu_a \lambda_{ra}\big) P$.

It is the formal reason behind the "digitisation" of errors in Preskill's Section 7.2: an
arbitrary interaction of $n$ qubits with their environment expands in the Pauli operators
(equation (7.12)), so a code that corrects the Pauli errors on $t$ qubits corrects every Kraus
operator supported on $t$ qubits, unitary errors and decoherence alike. For example, the
[bit-flip code](../bit-flip-and-shor-codes/is-correctable-bit-flip.md) corrects every
$c I + d X_1$, including a small coherent rotation of the first qubit.

## Sources

- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Theorem 3.1.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2, equations (7.11)–(7.13).
