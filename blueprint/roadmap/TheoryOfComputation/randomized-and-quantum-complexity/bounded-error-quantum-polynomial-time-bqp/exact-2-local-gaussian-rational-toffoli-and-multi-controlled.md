# Exact Gaussian-rational Toffoli and multi-controlled NOT decompositions

This node collects an exact decomposition of the Toffoli gate into two-qubit gates with Gaussian-rational entries, and
the resulting multiply-controlled NOT construction.

## Expansion

A sound expansion has separate pages for:

1. **Toffoli decomposition.** For $N \ge 3$ and pairwise distinct qubits $a, b, c < N$, in any order, the five well-formed
   encoded 2-local gates controlled-$V$ on $(b, c)$, CNOT on $(a, b)$, controlled-$V^*$ on $(b, c)$, CNOT on $(a, b)$ and
   controlled-$V$ on $(a, c)$, with $V = \sqrt X = \tfrac12 \begin{pmatrix} 1+i & 1-i \\ 1-i & 1+i \end{pmatrix}$ and each gate's control and
   target orientation encoded in its unitary $4 \times 4$ Gaussian-rational matrix (a gate acts on qubits $i < j$), applied in
   this order map every basis state $\lvert s \rangle$ to $\lvert s \oplus s_a s_b 2^c \rangle$, where $s_q$ is bit $q$ of $s$: exactly, with
   no phase and no workspace.
2. **Multiply-controlled NOT.** For $k \ge 2$ controls and $k - 2$ additional clean ancilla qubits, distinct from the controls
   and the target and initialized to $0$, a list of $O(k)$ such gates implements the $k$-controlled NOT and returns
   every ancilla to $0$; for $k \ge 3$, $4(k-2)$ Toffoli gates suffice, so $20(k-2)$ two-qubit gates.

## Depends on

- [Encoded 2-local quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate.md)
- [Well-formed quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate-well-formed.md)
- [Applying a quantum circuit to a state](../../complexity-classes/time-and-space-complexity-classes/apply-circuit.md)

## Related topics

- [Applying a 2-local gate to a state](../../complexity-classes/time-and-space-complexity-classes/apply-gate.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, "Elementary gates for quantum computation", arXiv:quant-ph/9503016 (Phys. Rev. A 52 (1995), 3457), Lemma 6.1 (a $\wedge_2(U)$ gate from controlled-$V$, CNOT, controlled-$V^\dagger$, CNOT, controlled-$V$ with $V^2 = U$), applied with $U = X$ and $V = \sqrt X$, and Lemma 7.2 (for $n \ge 5$ and $3 \le m \le \lceil n/2 \rceil$, a $\wedge_m(\sigma_x)$ gate from $4(m-2)$ Toffoli gates). <https://arxiv.org/abs/quant-ph/9503016>
