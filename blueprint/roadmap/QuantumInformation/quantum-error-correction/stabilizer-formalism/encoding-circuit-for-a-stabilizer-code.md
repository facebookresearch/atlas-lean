# Encoding circuit for a stabilizer code

Let $S$ be a stabilizer group on $n$ qubits with $n - k$ independent generators in
[standard form](standard-form-of-a-stabilizer-code.md) with $X$-rank $r$: generators $M_1, \dots, M_r$ whose $X$ part has a
single $1$ among the first $r$ qubits, at qubit $i$, and whose $Z$ part vanishes on qubits $r + 1, \dots, n - k$ (the block
$C_1 = 0$, which multiplying $M_1, \dots, M_r$ by products of $M_{r+1}, \dots, M_{n-k}$ achieves), and generators $M_{r+1}, \dots, M_{n-k}$ made of $Z$'s, where $M_{r+j}$
acts by $Z$ on qubit $r + j$ and by $I$ on the other qubits $r + 1, \dots, n - k$. Write each generator as
$M_i = \varepsilon_i\, i^{a_i \cdot b_i} X^{a_i} Z^{b_i}$ with sign $\varepsilon_i = \pm 1$. Let
$\bar X_1, \dots, \bar X_k$ be [logical $X$ operators](logical-pauli-operators-of-a-stabilizer-code.md) in standard form:
$\bar X_j$ acts by $Z$'s on the first $r$ qubits, by $X$'s on qubits $r + 1, \dots, n - k$, and by $X$ on qubit $n - k + j$
alone among the last $k$. Let $x_0 \in \mathbb{F}_2^n$ have a $1$ exactly at the qubits $r + j$ with $\varepsilon_{r+j} = -1$.
Then the encoding

$$|0 \dots 0\rangle |c_1 \dots c_k\rangle \;\longmapsto\; \lambda\, \bar X_1^{c_1} \cdots \bar X_k^{c_k} \sum_{M \in S} M\, |x_0\rangle
\qquad (c \in \mathbb{F}_2^k),$$

with the data on the last $k$ qubits and $\lambda = 2^{-(n - k - r) - r/2}$, is unitary on its domain, its image is an orthonormal basis
of the code space on which $\bar X_j$ acts as the bit flip of $c_j$, and it is performed by a circuit of at most $n - k$
single-qubit gates and at most

$$k(n - k - r) + r(n - 1) \;\le\; n(n - k)$$

two-qubit gates, each a CNOT or a controlled $Z$ or controlled $XZ$. For $S = \langle -Z_1 \rangle$ on two qubits the seed
$x_0 = 10$ is needed: $\sum_{M \in S} M |00\rangle = (I - Z_1)|00\rangle = 0$.

Construction: (1) apply $X$ to the qubits in the support of $x_0$; (2) apply the $X$ part of each $\bar X_j$ on qubits
$r + 1, \dots, n - k$, controlled on data qubit $n - k + j$, by CNOTs; (3) for $i = 1, \dots, r$ in turn, apply to qubit $i$
the Hadamard gate followed by $\operatorname{diag}(1, \varepsilon_i\, i^{a_i \cdot b_i})$, combined into one gate, and then
$M_i$ with its factor on qubit $i$ removed, controlled on qubit $i$, as one controlled $X$, $Z$ or $XZ$ per other qubit.
Proof: before step (3) qubit $i$ is still $|0\rangle$, since earlier steps act on it at most by controlled $Z$, and for any
state $|\varphi\rangle$ of the other qubits, step (3) for $i$ maps $|0\rangle_i |\varphi\rangle$ to
$2^{-1/2}(I + M_i)\, |0\rangle_i |\varphi\rangle$, because $X Z^{b} |0\rangle = |1\rangle$. The $\bar X_j$ commute with every
$M \in S$, and $X^{x_0}$ commutes with $M_1, \dots, M_r$ (their $Z$ parts vanish on qubits $r + 1, \dots, n - k$) and makes
$|x_0\rangle$ a $+1$ eigenvector of every $M_{r+j}$, so the sum over the whole group, whose $2^{n-k}$ elements are the products of the generators,
factors as $\sum_{M \in S} M \bar X^c |x_0\rangle = \prod_{j} (I + M_{r+j}) \prod_{i \le r} (I + M_i) \bar X^c |x_0\rangle
= 2^{n-k-r} \prod_{i \le r} (I + M_i) \bar X^c |x_0\rangle$. The circuit produces
$\prod_{i \le r} 2^{-1/2}(I + M_i) \bar X^c |x_0\rangle$, which is $\lambda$ times the group sum. In the example
$S = \langle -Z_1 \rangle$, $n - k - r = 1$ and $r = 0$, the group sum is $2|10\rangle$ and $\lambda = 1/2$; a unitary circuit maps the $2^k$ orthonormal inputs to $2^k$
orthonormal vectors of the $2^k$-dimensional code space.

## Depends on

- [Standard form of a stabilizer code](standard-form-of-a-stabilizer-code.md)
- [Logical Pauli operators of a stabilizer code](logical-pauli-operators-of-a-stabilizer-code.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Proof depends on

- [Standard form of a stabilizer code](standard-form-of-a-stabilizer-code.md)

## Sources

- R. Cleve and D. Gottesman, *Efficient computations of encodings for quantum error correction*, Phys. Rev. A 56 (1997), 76–82, arXiv:quant-ph/9607030, Section III (standard form) and Section IV (gate arrays: each generator applied conditioned on its pivot qubit, phases inserted as conditional phase shifts, and the bound $r_1 k + (n - 1) b \le (n - 1) d$ on two-qubit operations); its examples have all phases $+1$.
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 4.2, equations (4.7)–(4.13), with the author's errata to Chapter 4 (Hadamards placed just before the control dots, controlled-$XZ$ in place of controlled-$Y$, and generators of sign $-1$ handled by a tensor product Pauli operator), <https://perimeterinstitute.ca/personal/dgottesman/thesis-errata.html>.
