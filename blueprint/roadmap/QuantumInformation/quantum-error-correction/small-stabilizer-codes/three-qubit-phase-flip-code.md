# Three-qubit phase-flip code

Let $|\pm\rangle = \tfrac{1}{\sqrt 2}(|0\rangle \pm |1\rangle)$. The three-qubit phase-flip code is the two-dimensional
subspace of three qubits spanned by $|{+}{+}{+}\rangle$ and $|{-}{-}{-}\rangle$, with encoding
$a|0\rangle + b|1\rangle \mapsto a|{+}{+}{+}\rangle + b|{-}{-}{-}\rangle$. It is the stabilizer code of the group generated
by $X_1 X_2$ and $X_2 X_3$, and it is the image of the [bit-flip code](../bit-flip-and-shor-codes/code-projector.md)
under $H^{\otimes 3}$, which exchanges $|0\rangle, |1\rangle$ with $|+\rangle, |-\rangle$. A phase flip $Z$ on one qubit
exchanges $|+\rangle$ and $|-\rangle$ there, as a bit flip exchanges $|0\rangle$ and $|1\rangle$ in the bit-flip code. Shor's
nine-qubit code is the concatenation of this code (outside) with the bit-flip code (inside).

## Depends on

- [Code space of the three-qubit bit-flip code](../bit-flip-and-shor-codes/code-projector.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.15.1, equation (7.202) (the "phase code", the Hadamard-rotated repetition code), and Exercise 7.1(b).
