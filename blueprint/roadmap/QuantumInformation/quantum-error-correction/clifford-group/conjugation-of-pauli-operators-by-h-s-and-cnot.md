# Conjugation of Pauli operators by $H$, $S$ and CNOT

Let $H = \tfrac{1}{\sqrt 2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$, $S = \operatorname{diag}(1, i)$, $Y = iXZ$, and let
CNOT act on two qubits by $|x, y\rangle \mapsto |x, x \oplus y\rangle$ (first qubit control). Then

$$H X H^{*} = Z, \quad H Z H^{*} = X, \quad H Y H^{*} = -Y; \qquad S X S^{*} = Y, \quad S Z S^{*} = Z, \quad S Y S^{*} = -X;$$

$$\mathrm{CNOT}\,(X \otimes I)\,\mathrm{CNOT} = X \otimes X, \quad \mathrm{CNOT}\,(I \otimes X)\,\mathrm{CNOT} = I \otimes X,$$

$$\mathrm{CNOT}\,(Z \otimes I)\,\mathrm{CNOT} = Z \otimes I, \quad \mathrm{CNOT}\,(I \otimes Z)\,\mathrm{CNOT} = Z \otimes Z.$$

So $H$, $S$ and CNOT map Pauli operators to Pauli operators under conjugation: they lie in the Clifford group. Under
CNOT bit flips propagate from control to target and phase flips from target to control. Each identity is a $2 \times 2$
or $4 \times 4$ matrix computation; conjugation is multiplicative, which gives the images of products such as $Y$.

## Depends on

- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)
- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 5.3, equations (5.5)–(5.11).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.5, equations (64)–(65).
