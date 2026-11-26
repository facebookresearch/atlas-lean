# Quantum bit commitments in canonical form

A *non-interactive quantum bit commitment in canonical form* is a pair of quantum polynomial-time unitaries $(Q_0,Q_1)$ acting on registers $\mathsf{C}$ (commitment) and $\mathsf{R}$ (reveal). To commit to $b$, the sender prepares $Q_b|0\rangle_{\mathsf{CR}}$ and sends $\mathsf{C}$; to open, it sends $b$ and $\mathsf{R}$, and the receiver applies $Q_b^{\dagger}$ and checks for $|0\rangle$. The scheme is *computationally (resp. statistically) hiding* if the reduced states $\rho_b=\mathrm{Tr}_{\mathsf{R}}(Q_b|0\rangle\langle 0|Q_b^{\dagger})$ are computationally (resp. statistically) indistinguishable, and *statistically (resp. computationally) binding* if no (efficient) operation on $\mathsf{R}$ can map $Q_0|0\rangle$ close to $Q_1|0\rangle$, measured by fidelity.

## Depends on

- [The binding experiment](../../../ComputerScience/cryptography/signatures-and-protocols/commitment-schemes/the-computational-binding-game-for-keyed-commitm/binding-game.md)
- [Monotonicity of fidelity under channels](../../../QuantumInformation/quantum-operations/monotonicity-of-fidelity-under-channels.md)
- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Jun Yan, "General Properties of Quantum Bit Commitments", ASIACRYPT (2022), IACR ePrint 2020/1488.
- Tomoyuki Morimae, Takashi Yamakawa, "Quantum Commitments and Signatures without One-Way Functions", CRYPTO (2022), arXiv:2112.06369.
