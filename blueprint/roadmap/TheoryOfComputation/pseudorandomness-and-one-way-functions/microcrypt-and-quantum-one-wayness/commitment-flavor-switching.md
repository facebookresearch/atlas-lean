# Hiding–binding duality for canonical quantum commitments

Let $(Q_0,Q_1)$ be a canonical quantum commitment on registers $(\mathsf{C},\mathsf{R})$. The *dual* commitment swaps the roles of the registers, committing with $\mathsf{R}$ and revealing with $\mathsf{C}$ (with suitable controlled phases). If $(Q_0,Q_1)$ is computationally hiding and statistically binding, its dual is statistically hiding and computationally binding, and vice versa. Moreover, the honest-binding notion for canonical commitments implies the stronger sum-binding notion $\Pr[\text{open }0]+\Pr[\text{open }1]\le 1+\mathrm{negl}$.

## Proof sketch

Statistical binding of the original is a statement about the fidelity between $\rho_0$ and $\rho_1$ on $\mathsf{C}$ being small after any operation on $\mathsf{R}$, which by Uhlmann's theorem is equivalent to the reduced states on $\mathsf{R}$ (the dual's commitment register) being close, i.e., statistical hiding of the dual. Computational versions follow by the same correspondence restricted to efficient operations, using an Uhlmann-type unitary for the reduction.

## Depends on

- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [Monotonicity of fidelity under channels](../../../QuantumInformation/quantum-operations/monotonicity-of-fidelity-under-channels.md)

## Sources

- Jun Yan, "General Properties of Quantum Bit Commitments", ASIACRYPT (2022), IACR ePrint 2020/1488.
