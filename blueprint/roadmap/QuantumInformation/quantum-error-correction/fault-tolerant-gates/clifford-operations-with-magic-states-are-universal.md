# Clifford operations with magic states are universal

Consider circuits built from preparation of $|0\rangle$, the gates $H$, $S$ and CNOT, measurements in the computational
basis, gates chosen as functions of earlier measurement outcomes, and copies of the [magic state](magic-state.md)
$|A\rangle$. Every gate of the [universal gate set](../universal-gate-sets/universal-gate-set.md)
$\{H, T, \mathrm{CNOT}\}$ is implemented exactly by such a circuit, with one copy of $|A\rangle$ per $T$ gate. Hence for every
unitary $U$ on $n$ qubits and every $\varepsilon > 0$ some such circuit, using finitely many magic states, implements a
unitary within $\varepsilon$ of $U$ up to a global phase. Without magic states the same operations, with classical control by an
efficient algorithm, are classically simulable (the Gottesman–Knill theorem).

Proof: [magic-state injection](magic-state-injection.md) implements $T$, and
[Clifford plus $T$ is universal](../universal-gate-sets/clifford-plus-t-is-universal.md). Bravyi and Kitaev prove the
same with $|H\rangle$-type states and also with $T$-type magic states, in a model that allows measuring any one-qubit
Pauli operator.

## Depends on

- [Magic states](magic-state.md)
- [Universal gate set](../universal-gate-sets/universal-gate-set.md)

## Proof depends on

- [Magic-state injection](magic-state-injection.md)
- [Clifford plus $T$ is universal](../universal-gate-sets/clifford-plus-t-is-universal.md)
- [Gottesman–Knill theorem](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/gottesmanknill-theorem.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section III ("the sets of operations $O_{\mathrm{ideal}} \cup \{|H\rangle\}$ and $O_{\mathrm{ideal}} \cup \{|T\rangle\}$ are sufficient for universal quantum computation").
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5.
