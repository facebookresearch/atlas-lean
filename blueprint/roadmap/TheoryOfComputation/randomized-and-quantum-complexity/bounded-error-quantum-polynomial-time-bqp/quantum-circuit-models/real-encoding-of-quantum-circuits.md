# Simulating complex quantum circuits by real circuits with one extra qubit

Encode an $m$-qubit state $\psi=\sum_x(a_x+ib_x)|x\rangle$ as the $(m+1)$-qubit real state $\sum_x a_x|x\rangle|0\rangle+b_x|x\rangle|1\rangle$. An operator $\sum_{x,x'}(a_{x,x'}+ib_{x,x'})|x\rangle\langle x'|$ is replaced by $\sum_{x,x'}|x\rangle\langle x'|\otimes(a_{x,x'}I+b_{x,x'}XZ)$, that is, each complex entry $a+ib$ becomes the real block $\begin{pmatrix}a&-b\\b&a\end{pmatrix}$ acting on the extra qubit. The replaced operator maps the encoding of every input vector to the encoding of the corresponding output vector, inner products of encodings are the real parts of the original inner products, unitaries go to (real) unitaries, positive semidefinite operators to positive semidefinite operators, and measurement outcome probabilities are unchanged. Consequently circuits with complex gates (such as phase gates) are simulated by real circuits with one extra qubit, which is why universality of a real gate set for real orthogonal operators, such as Toffoli with Hadamard, gives universality for quantum computation.

## Proof sketch

$XZ$ applied to the extra qubit multiplies the encoded state by $i$. The map $a+ib\mapsto\begin{pmatrix}a&-b\\b&a\end{pmatrix}$ is an injective ring homomorphism compatible with conjugate transposition (derived formulation), so it preserves products, adjoints and unitarity; measurement probabilities add the squared real and imaginary parts.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)

## Sources

- Matthew McKague, Michele Mosca and Nicolas Gisin, "Simulating Quantum Systems Using Real Hilbert Spaces", Physical Review Letters 102, 020505, 2009 (arXiv:0810.1923), Section II.A, Eqs. (1)–(3), and Section II.B.
- Yaoyun Shi, "Both Toffoli and Controlled-NOT Need Little Help to Universal Quantum Computing", Quantum Information and Computation 3(1), 84–92, 2003 (numbering of arXiv:quant-ph/0205115), Section 1 and Theorem 1.1.
- Dorit Aharonov, "A Simple Proof that Toffoli and Hadamard are Quantum Universal", arXiv:quant-ph/0301040, 2003 (unrefereed; supplementary).
- Ethan Bernstein and Umesh Vazirani, "Quantum Complexity Theory", SIAM Journal on Computing 26(5), 1411–1473, 1997 (real amplitudes suffice).
