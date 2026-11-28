# Exact universality of CNOT and single-qubit gates

Let $n \ge 1$. Every unitary $U$ on $(\mathbb{C}^2)^{\otimes n}$ is exactly equal to a finite product of gates each of which is either a single-qubit unitary acting on one
qubit or a controlled-NOT acting on an ordered pair of distinct qubits (with the identity on the remaining qubits), using no ancilla qubits. The construction
proceeds in two stages: $U$ is a finite product of two-level unitaries, each acting nontrivially only on the span of two computational basis states,
namely at most $2^{n-1}(2^n - 1)$ two-level unitaries followed by a diagonal phase matrix $D$, and $D$ is itself the product of $2^{n-1}$ two-level
unitaries, each the diagonal phase matrix of $D$ restricted to one pair of basis states of a fixed pairing; then each two-level unitary is a finite product of
controlled-NOT and single-qubit gates. No global phase remains, since $D$ carries every phase exactly. The construction uses $O(n^3 4^n)$ gates.
Approximate synthesis from a finite gate set (Solovay–Kitaev) is a different statement.

## Depends on

- [Unitary evolution and elementary gates](unitary-evolution-and-elementary-gates.md)
- [Decomposition of a unitary into two-level unitaries](../quantum-error-correction/universal-gate-sets/decomposition-into-two-level-unitaries.md)
- [A diagonal unitary is a product of two-level diagonal unitaries](../quantum-error-correction/universal-gate-sets/diagonal-unitary-as-a-product-of-two-level-unitaries.md)

## Proof depends on

- [A two-level unitary from multiply controlled gates along a Gray code](../quantum-error-correction/universal-gate-sets/two-level-unitary-from-multiply-controlled-gates-along-a-gray-code.md)
- [Multiply controlled unitaries from CNOT and single-qubit gates](../quantum-error-correction/universal-gate-sets/multiply-controlled-unitary-from-cnot-and-single-qubit-gates.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467; arXiv:quant-ph/9503016, Abstract and Section 8 (the Reck et al. decomposition $U = (\prod T(x_1, x_2))\, D$ into two-level rotations and a diagonal phase matrix, each rotation conjugated by Gray-code controlled-NOTs to a $\wedge_{n-1}(U)$ gate, with $D$ a product of $2^{n-1}$ two-dimensional rotations, giving an exact simulation of any unitary on $n$ bits by $\Theta(n^3 4^n)$ gates with no work bits, each $\wedge_{n-1}$ gate counted by Corollary 7.6), Lemma 7.5 and Corollary 7.6 ($\wedge_{n-1}(U)$ in $\Theta(n^2)$ basic operations). <https://arxiv.org/abs/quant-ph/9503016>
