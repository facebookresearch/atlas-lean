# Pseudorandom states with long outputs are one-way state generators

Let $\{|\phi_k\rangle\}_{k\in\{0,1\}^{\lambda}}$ be a PRS generator on $n\ge\lambda+\omega(\log\lambda)$ qubits. Then $(\mathsf{KeyGen},\mathsf{StateGen},\mathsf{Ver})$ with $\mathsf{Ver}(k',\rho)$ the projective test onto $|\phi_{k'}\rangle$ is a one-way state generator: no quantum polynomial-time adversary, given $t$ copies of $|\phi_k\rangle$, outputs $k'$ passing verification on a fresh copy with non-negligible probability.

## Proof sketch

Suppose $\mathcal{A}$ succeeds with probability $\epsilon$. Distinguish $|\phi_k\rangle^{\otimes(t+1)}$ from Haar copies by running $\mathcal{A}$ on $t$ copies and testing the last copy against $|\phi_{k'}\rangle$ (preparable from $k'$). On Haar inputs, the expected maximal overlap of a Haar-random state with any of the $2^{\lambda}$ states $|\phi_{k'}\rangle$ is at most $2^{\lambda}\cdot 2^{-n}$ in expectation over the test, which is negligible for $n\ge\lambda+\omega(\log\lambda)$, so the distinguishing advantage is about $\epsilon$.

## Depends on

- [Pseudorandom quantum state generators](../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)
- [One-way state generators](one-way-state-generators.md)

## Sources

- Tomoyuki Morimae, Takashi Yamakawa, "One-Wayness in Quantum Cryptography", TQC (2024), arXiv:2210.03394.
- Tomoyuki Morimae, Takashi Yamakawa, "Quantum Commitments and Signatures without One-Way Functions", CRYPTO (2022), arXiv:2112.06369.
