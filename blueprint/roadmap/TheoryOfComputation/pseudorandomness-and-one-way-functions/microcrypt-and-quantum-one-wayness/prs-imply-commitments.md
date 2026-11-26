# Quantum commitments from pseudorandom states

If pseudorandom quantum state generators with output length $n\ge 3\lambda$ exist, then there exist non-interactive quantum bit commitments (for classical bits) that are computationally hiding and statistically binding. Since PRS may exist relative to an oracle where $\mathsf{BQP}=\mathsf{QMA}$ (and, for single-copy PRS, where $\mathsf{P}=\mathsf{NP}$), quantum commitments may exist even if no quantum-secure classical cryptographic primitive exists. Pseudorandom function-like states likewise imply one-time-secure symmetric encryption of quantum states, pseudo one-time pads and statistically binding commitments, and enable secure computation.

## Proof sketch

Commit to $0$ by sending the mixed state $\mathbb{E}_k|\phi_k\rangle\langle\phi_k|^{\otimes t}$ (purified with the key register) and to $1$ by sending a maximally mixed state on the symmetric subspace (Haar average); hiding is pseudorandomness. Statistical binding: the PRS mixture has rank at most $2^{\lambda}$ while the Haar mixture on $n\ge 3\lambda$ qubits is nearly maximally mixed, so their fidelity is at most about $2^{\lambda-n}$, small for $n\ge 3\lambda$.

## Depends on

- [Pseudorandom quantum state generators](../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)
- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [Monotonicity of fidelity under channels](../../../QuantumInformation/quantum-operations/monotonicity-of-fidelity-under-channels.md)

## Sources

- Tomoyuki Morimae, Takashi Yamakawa, "Quantum Commitments and Signatures without One-Way Functions", CRYPTO (2022), arXiv:2112.06369.
- Prabhanjan Ananth, Luowen Qian, Henry Yuen, "Cryptography from Pseudorandom Quantum States", CRYPTO (2022), arXiv:2112.10020.
