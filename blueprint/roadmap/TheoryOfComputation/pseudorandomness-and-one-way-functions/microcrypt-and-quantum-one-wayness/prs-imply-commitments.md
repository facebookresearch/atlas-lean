# Quantum commitments from pseudorandom states

If pseudorandom quantum state generators with output length $n\ge c\lambda$ for a constant $c>1$ exist ($\lambda$ the key length), then there exist non-interactive quantum bit commitments (for classical bits) that are computationally hiding and statistically binding; the construction uses only single-copy security of the generator. Since PRS exist relative to a quantum oracle where $\mathsf{BQP}=\mathsf{QMA}$, and single-copy PRS relative to a classical oracle where $\mathsf{P}=\mathsf{NP}$, quantum commitments may exist even if no quantum-secure classical cryptographic primitive exists. Pseudorandom function-like states likewise imply a one-time-secure encryption scheme for classical messages longer than the key, with quantum ciphertexts (the quantum pseudo one-time pad), and statistically binding commitments, and hence secure computation.

## Proof sketch

Let $|\phi_k\rangle$ be the $n$-qubit output on key $k\in\{0,1\}^{\lambda}$ and $P_{x,z}=X^{x}Z^{z}$. To commit to $b$, prepare $2^{-(2n+\lambda)/2}\sum_{x,z\in\{0,1\}^n}\sum_{k}|x,z,k\rangle_R\otimes P_{x,z}^{\,b}|\phi_k\rangle_C$ and send $C$; to open, send $b$ and $R$, and the receiver projects onto the honest state. The commitment register holds $\rho_0=2^{-\lambda}\sum_k|\phi_k\rangle\langle\phi_k|$ for $b=0$ and, by the quantum one-time pad, the maximally mixed state $I/2^n$ for $b=1$, which is also the average of one Haar-random state; so hiding is single-copy pseudorandomness. Statistical binding: $\rho_0$ has rank at most $2^{\lambda}$, so its fidelity with $I/2^n$ is at most $2^{\lambda-n}$, and monotonicity of fidelity bounds the two opening probabilities of any sender by $p_0+p_1\le 1+2^{-(n-\lambda)/2}$, which is negligible for $n\ge c\lambda$ with $c>1$.

## Depends on

- [Pseudorandom quantum state generators](../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)
- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [Monotonicity of fidelity under channels](../../../QuantumInformation/quantum-operations/monotonicity-of-fidelity-under-channels.md)

## Sources

- Tomoyuki Morimae, Takashi Yamakawa, "Quantum Commitments and Signatures without One-Way Functions", CRYPTO (2022), arXiv:2112.06369.
- Prabhanjan Ananth, Luowen Qian, Henry Yuen, "Cryptography from Pseudorandom Quantum States", CRYPTO (2022), arXiv:2112.10020.
- William Kretschmer, Luowen Qian, Makrand Sinha, Avishay Tal, "Quantum Cryptography in Algorithmica", STOC (2023), arXiv:2212.00879.
