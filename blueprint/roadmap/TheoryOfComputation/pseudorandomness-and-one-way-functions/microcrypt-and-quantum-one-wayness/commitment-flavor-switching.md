# Hiding–binding duality for canonical quantum commitments

Let $(Q_0,Q_1)$ be a canonical quantum commitment on registers $(\mathsf{C},\mathsf{R})$. In the single-call dual compiler of Hhan–Morimae–Yamakawa (EUROCRYPT 2023, Theorem 6.1), the **dual** commitment swaps the roles of the registers (setting $\mathsf{C}' := (\mathsf{R},\mathsf{D})$, $\mathsf{R}' := \mathsf{C}$, and $Q'_b := (Q_0\otimes|0\rangle\langle 0|_{\mathsf{D}} + Q_1\otimes|1\rangle\langle 1|_{\mathsf{D}})(I\otimes Z_{\mathsf{D}}^b H_{\mathsf{D}})$), so that if $(Q_0,Q_1)$ is computationally hiding and statistically binding, its dual is statistically hiding and computationally binding, and vice versa. Yan (ASIACRYPT 2022) establishes the existence equivalence of the two flavours via a multi-copy parallel compiler based on a simplified Crépeau–Legré–Salvail protocol and round collapse (Theorem 7), and proves that honest-binding for canonical commitments is equivalent to sum-binding $\Pr[\text{open }0]+\Pr[\text{open }1]\le 1+\mathrm{negl}$ (Theorem 2).

## Proof sketch

For the dual compiler of Hhan–Morimae–Yamakawa (Theorem 6.1), statistical binding of the original commitment corresponds to small fidelity between the reduced states $\rho_0, \rho_1$ on $\mathsf{C}$ after any operation on $\mathsf{R}$, which by Uhlmann's theorem corresponds to closeness on the swapped commitment register (statistical hiding of the dual), and computational security transfers symmetrically via an Uhlmann-type reduction. Yan's existence equivalence (Theorem 7) instead runs $n$ parallel copies through a BB84-style interactive protocol and collapses rounds back to canonical form.

## Depends on

- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [Monotonicity of fidelity under channels](../../../QuantumInformation/quantum-operations/monotonicity-of-fidelity-under-channels.md)

## Sources

- Minki Hhan, Tomoyuki Morimae, Takashi Yamakawa, "From the Hardness of Detecting Superpositions to Cryptography: Quantum Public Key Encryption and Commitments", EUROCRYPT (2023), arXiv:2210.05978 (Theorem 6.1).
- Jun Yan, "General Properties of Quantum Bit Commitments", ASIACRYPT (2022), IACR ePrint 2020/1488 (Theorems 2 and 7).
