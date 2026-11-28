# Symplectic product of Pauli operators

For $a, b, a', b' \in \mathbb{F}_2^n$, the symplectic product of the pairs $(a, b)$ and $(a', b')$ is

$$\omega\big((a, b), (a', b')\big) = a \cdot b' + a' \cdot b \in \mathbb{F}_2, \qquad u \cdot v = \sum_{i=1}^n u_i v_i \bmod 2.$$

It is a bilinear form on $\mathbb{F}_2^{2n}$ with $\omega(v, v) = 0$ for every $v$, and it is nondegenerate: if
$\omega(v, w) = 0$ for all $w$ then $v = 0$. The pair $(a, b)$ records the [Pauli operator](../css-codes/pauli.md)
$X^a Z^b$, which acts by $X$ on the qubits in the support of $a$ and by $Z$ on those in the support of $b$ (by
$XZ = -iY$ where both supports meet); every element of the $n$-qubit Pauli group is $c\, X^a Z^b$ with
$c \in \{\pm 1, \pm i\}$, so modulo phases the Pauli group is the vector space $\mathbb{F}_2^{2n}$ and products of
Pauli operators correspond to sums of vectors.

Writing the $Z$ part first, $Z^b X^a = (-1)^{a \cdot b} X^a Z^b$ is the same operator only up to sign: it is the same
element of the Pauli group modulo phases, and the symplectic product does not depend on the order. Throughout, $(a, b)$
names the operator $X^a Z^b$ itself; statements about other representatives hold up to phase.

## Depends on

- [Pauli operator $X^a Z^b$ on $n$ qubits](../css-codes/pauli.md)
- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.2, equations (7.126)–(7.130).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.4, equation (3.23).
- A. R. Calderbank, E. M. Rains, P. W. Shor and N. J. A. Sloane, *Quantum error correction via codes over GF(4)*, IEEE Trans. Inform. Theory 44 (1998), 1369–1387, arXiv:quant-ph/9608006, Section 2, equation (1).
