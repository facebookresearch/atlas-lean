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
(Lemma 1), which excludes $n = 2$ (Theorem 2), and $n = 3$ reduces to $n = 2$ (Theorem 3); numbers as in the journal article.

## Expansion

The minimality proof uses two results that need their own pages: Grassl, Beth and Pellizzari's Theorem 1, that a code
correcting one erasure in which one code state has a one-qubit tensor factor has it in every code state, so the code can be
shortened by that qubit; and their Lemma 1, that every two-dimensional subspace of two qubits contains a product state
(the determinant of $A + tB$ for $2 \times 2$ coefficient matrices $A, B$ has a root, or $B$ is singular). This page becomes
ready once both are linked under Proof depends on.

## Depends on

- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md)
- [A code of distance $d$ corrects $d - 1$ erasures](../distance-of-a-quantum-code/distance-d-code-corrects-d-minus-1-erasures.md)

## Proof depends on

- [Necessity of the Knill–Laflamme conditions](../knill-laflamme-conditions/knill-laflamme-of-is-correctable.md)
- [A code of distance $d$ corrects $d - 1$ erasures](../distance-of-a-quantum-code/distance-d-code-corrects-d-minus-1-erasures.md)

## Background

- [The quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md)

## Sources

- M. Grassl, Th. Beth and T. Pellizzari, *Codes for the quantum erasure channel*, Phys. Rev. A 56 (1997), 33–38, arXiv:quant-ph/9610042; in the journal article Section III.A (conditions), Section III.B (the four-qubit code) and Section III.C (minimality: Theorem 1, Lemma 1, Theorems 2 and 3); the arXiv version numbers these Lemma 3 and Theorems 4 and 5.
