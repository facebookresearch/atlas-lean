# A controlled single-qubit unitary from two CNOTs and four single-qubit gates

For a unitary $2 \times 2$ matrix $U$ let $\wedge_1(U)$ be the two-qubit gate that applies $U$ to the second (target) qubit
when the first (control) qubit is $|1\rangle$ and does nothing when it is $|0\rangle$. Then $\wedge_1(U)$ is a product of at
most six gates: four single-qubit gates and two CNOTs from the control to the target.

For $W \in SU(2)$ with $A, B, C$ as in the [$ABC$ decomposition](abc-decomposition-of-special-unitary-matrices.md),
$\wedge_1(W)$ is obtained by applying $C$ to the target, a CNOT, $B$ to the target, a CNOT and $A$ to the target: the
target receives $ABC = I$ when the control is $0$ and $AXBXC = W$ when it is $1$. Such a network with $A, B, C \in SU(2)$
simulates $\wedge_1(W)$ only if $W \in SU(2)$. A general unitary is $U = e^{i\delta} W$ with $W \in SU(2)$, and
$\wedge_1(e^{i\delta} I)$ is the single-qubit phase gate $\operatorname{diag}(1, e^{i\delta})$ on the control; merging it
with the other single-qubit gates gives the count.

## Depends on

- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)
- [The $ABC$ decomposition of a special unitary matrix](abc-decomposition-of-special-unitary-matrices.md)

## Proof depends on

- [The $ABC$ decomposition of a special unitary matrix](abc-decomposition-of-special-unitary-matrices.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 5, Lemma 5.1 (the network $A$, CNOT, $B$, CNOT, $C$, "if and only if $W \in SU(2)$"), Lemma 5.2 (the phase case) and Corollary 5.3 ("at most six basic gates: four 1-bit gates ... and two XOR gates").
