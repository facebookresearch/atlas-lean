# Encoding circuit for a stabilizer code

Let $S$ be a stabilizer group on $n$ qubits with $n - k$ independent generators $M_1, \dots, M_{n-k}$ in
[standard form](standard-form-of-a-stabilizer-code.md), with $X$-rank $r$, and let
$\bar X_1, \dots, \bar X_k$ be [logical $X$ operators](logical-pauli-operators-of-a-stabilizer-code.md) in Gottesman's
standard form (each acts on the last $k$ qubits only by $X$ on qubit $n - k + i$). Then the encoding

$$|0 \dots 0\rangle |c_1 \dots c_k\rangle \;\longmapsto\; \lambda\, \bar X_1^{c_1} \cdots \bar X_k^{c_k} \sum_{M \in S} M\, |0 \dots 0\rangle
\qquad (c \in \mathbb{F}_2^k),$$

with the data on the last $k$ qubits and $\lambda > 0$ the normalising constant, is performed by a circuit of at most
$r$ single-qubit gates (each a Hadamard gate, possibly followed by $Z$) and at most

$$k(n - k - r) + r(n - 1) \;\le\; n(n - k)$$

two-qubit gates, each a Pauli operator on one qubit controlled by another. The image is a basis of the code space on
which the $\bar X_i$ act as bit flips.

Construction: first apply the $\bar X_i$, controlled on the data qubit $n - k + i$, restricted to their $X$ part on
qubits $r + 1, \dots, n - k$; then apply a Hadamard to each of the first $r$ qubits and $M_i$ controlled on qubit $i$
($i \le r$). Generators made only of $Z$'s fix $|0 \dots 0\rangle$ and need no gates.

## Depends on

- [Standard form of a stabilizer code](standard-form-of-a-stabilizer-code.md)
- [Logical Pauli operators of a stabilizer code](logical-pauli-operators-of-a-stabilizer-code.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Proof depends on

- [Standard form of a stabilizer code](standard-form-of-a-stabilizer-code.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 4.2, equations (4.7)–(4.13) and Figure 4.2.
