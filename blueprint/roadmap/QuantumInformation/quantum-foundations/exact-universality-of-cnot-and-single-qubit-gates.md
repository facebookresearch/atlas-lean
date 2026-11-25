# Exact universality of CNOT and single-qubit gates

Let $n \ge 1$. Every unitary $U$ on $(\mathbb{C}^2)^{\otimes n}$ is exactly equal to a finite product of gates each of which is either a single-qubit unitary acting on one
qubit or a controlled-NOT acting on an ordered pair of distinct qubits (with the identity on the remaining qubits), using no ancilla qubits. The construction
proceeds in two stages: $U$ is a finite product of two-level unitaries, each acting nontrivially only on the span of two computational basis states,
namely at most $2^{n-1}(2^n - 1)$ two-level unitaries followed by a diagonal phase matrix $D$, and $D$ is itself the product of $2^{n-1}$ two-level
unitaries, each the diagonal phase matrix of $D$ restricted to one pair of basis states of a fixed pairing; then each two-level unitary is a finite product of
controlled-NOT and single-qubit gates. No global phase remains, since $D$ carries every phase exactly. The construction uses $O(n^3 4^n)$ gates.
Approximate synthesis from a finite gate set (Solovay–Kitaev) is a different statement.

## Expansion

A good expansion adds a page for each pending prerequisite below.

- Statement prerequisite: two-level unitaries, and the decomposition of every unitary on $\mathbb{C}^d$ into at most $d(d-1)/2$ two-level unitaries and a diagonal phase matrix (Givens-style factorization).
- Statement prerequisite: for even $d$, every diagonal unitary on $\mathbb{C}^d$ is a product of $d/2$ two-level diagonal unitaries acting on disjoint pairs of basis states.
- Proof prerequisite: every two-level unitary on $n$ qubits is a product of at most $2n - 1$ multiply-controlled gates $\wedge_{n-1}(V)$, conjugated by single-qubit NOT gates, along a Gray code joining its two basis states.
- Proof prerequisite: every multiply-controlled single-qubit unitary $\wedge_{m}(U)$ on $m + 1$ qubits is a finite product of controlled-NOT and single-qubit gates without ancillas, with $O(m^2)$ gates.

## Depends on

- [Unitary evolution and elementary gates](unitary-evolution-and-elementary-gates.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467; arXiv:quant-ph/9503016, Abstract and Section 8 (the Reck et al. decomposition $U = (\prod T(x_1, x_2))\, D$ into two-level rotations and a diagonal phase matrix, each rotation conjugated by Gray-code controlled-NOTs to a $\wedge_{n-1}(U)$ gate, with $D$ a product of $2^{n-1}$ two-dimensional rotations, giving an exact simulation of any unitary on $n$ bits by $\Theta(n^3 4^n)$ gates with no work bits, each $\wedge_{n-1}$ gate counted by Corollary 7.6), Lemma 7.5 and Corollary 7.6 ($\wedge_{n-1}(U)$ in $\Theta(n^2)$ basic operations). <https://arxiv.org/abs/quant-ph/9503016>
