# Simulating complex quantum circuits by real circuits with one extra qubit

Encode an $m$-qubit state $\psi$ as the $(m+1)$-qubit real state with amplitude $\operatorname{Re}\psi_x$ on $|x0\rangle$ and $\operatorname{Im}\psi_x$ on $|x1\rangle$. A matrix acts on encoded states by replacing each complex entry $a$ with the real block $\begin{pmatrix}\operatorname{Re}a&-\operatorname{Im}a\\\operatorname{Im}a&\operatorname{Re}a\end{pmatrix}$; this map is a ring homomorphism that preserves unitarity, norms and computational-basis measurement probabilities of the first $m$ qubits. Consequently circuits with phase gates (such as $Z$, $T$, controlled phases) are simulated by real circuits, and real gate sets such as Hadamard–Toffoli suffice for $\mathsf{BQP}$.

## Proof sketch

The map $a+ib\mapsto\begin{pmatrix}a&-b\\b&a\end{pmatrix}$ is an injective ring homomorphism compatible with conjugate transposition; measurement probabilities add the squared real and imaginary parts.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)

## Sources

- Yaoyun Shi, "Both Toffoli and Controlled-NOT Need Little Help to Universal Quantum Computing", Quantum Information and Computation 3(1), 84–92, 2003.
- Dorit Aharonov, "A Simple Proof that Toffoli and Hadamard are Quantum Universal", arXiv:quant-ph/0301040, 2003 (unrefereed; supplementary to Shi).
- Ethan Bernstein and Umesh Vazirani, "Quantum Complexity Theory", SIAM Journal on Computing 26(5), 1411–1473, 1997 (real amplitudes suffice).
