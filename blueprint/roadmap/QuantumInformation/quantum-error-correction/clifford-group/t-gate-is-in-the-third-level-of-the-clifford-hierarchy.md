# The $T$ gate is in the third level of the Clifford hierarchy

Let $T = \operatorname{diag}(1, e^{i\pi/4})$ and $S = T^2 = \operatorname{diag}(1, i)$. Then

$$T X T^{*} = \begin{pmatrix} 0 & e^{-i\pi/4} \\ e^{i\pi/4} & 0 \end{pmatrix} = e^{i\pi/4} X S^{*}, \qquad T Z T^{*} = Z .$$

Both are Clifford unitaries, and conjugation is multiplicative, so $T Q T^{*}$ is a Clifford unitary for every one-qubit
Pauli operator $Q$: $T$ lies in the third level $\mathcal{C}^{(3)}$ of the [Clifford hierarchy](clifford-hierarchy.md).
It does not lie in the Clifford group, since $T X T^{*}$ is not a scalar multiple of $I, X, Y$ or $Z$. The same holds
for $T$ acting on one qubit of $n$.

## Depends on

- [Clifford hierarchy](clifford-hierarchy.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5, equations (70)–(71).
