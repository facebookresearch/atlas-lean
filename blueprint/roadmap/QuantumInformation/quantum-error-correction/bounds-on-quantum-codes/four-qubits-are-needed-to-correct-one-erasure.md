# Four qubits are needed to correct one erasure

The least $n$ for which some two-dimensional subspace of $n$ qubits has
[distance at least $2$](../distance-of-a-quantum-code/has-distance-at-least.md), equivalently
[corrects one erasure](../distance-of-a-quantum-code/distance-d-code-corrects-d-minus-1-erasures.md) (any error on one
known qubit), is $n = 4$. For $n = 4$ the span of

$$|\bar 0\rangle = \tfrac{1}{\sqrt 2}(|0000\rangle + |1111\rangle), \qquad |\bar 1\rangle = \tfrac{1}{\sqrt 2}(|1001\rangle + |0110\rangle)$$

works; no two-dimensional subspace of two or three qubits does. The [quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md)
$k + 2(d - 1) \le n$ would allow $n = 3$, so it is not attained here.

Proof (Grassl, Beth and Pellizzari): both codewords and their Hadamard transforms have only even-weight components, so a
single bit flip is detected in both bases. Conversely, a code correcting one erasure that has a one-qubit factor in one
code state has it in all (their Theorem 1); every two-dimensional subspace of two qubits contains a product state
(Lemma 3), which excludes $n = 2$ (Theorem 4), and $n = 3$ reduces to $n = 2$ (Theorem 5).

## Depends on

- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md)
- [A code of distance $d$ corrects $d - 1$ erasures](../distance-of-a-quantum-code/distance-d-code-corrects-d-minus-1-erasures.md)

## Proof depends on

- [Necessity of the Knill–Laflamme conditions](../knill-laflamme-conditions/knill-laflamme-of-is-correctable.md)
- [A code of distance $d$ corrects $d - 1$ erasures](../distance-of-a-quantum-code/distance-d-code-corrects-d-minus-1-erasures.md)

## Background

- [The quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md)

## Sources

- M. Grassl, Th. Beth and T. Pellizzari, *Codes for the quantum erasure channel*, Phys. Rev. A 56 (1997), 33–38, arXiv:quant-ph/9610042, Section II.B (the four-qubit code) and Section II.C, Theorems 1, 4 and 5.
