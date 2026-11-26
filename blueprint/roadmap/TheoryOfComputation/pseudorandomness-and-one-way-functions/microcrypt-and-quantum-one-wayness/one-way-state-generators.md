# One-way state generators

A *one-way state generator (OWSG)* consists of quantum polynomial-time algorithms $\mathsf{KeyGen}(1^\lambda)\to k$ (classical key), $\mathsf{StateGen}(k)\to|\phi_k\rangle$ (pure state) and a verification procedure $\mathsf{Ver}(k',|\phi_k\rangle)$ that projects onto $|\phi_{k'}\rangle$, such that for every quantum polynomial-time adversary $\mathcal{A}$ and polynomial $t$,

$$
\Pr\bigl[k\leftarrow\mathsf{KeyGen},\ k'\leftarrow\mathcal{A}(|\phi_k\rangle^{\otimes t}):\ \mathsf{Ver}(k',|\phi_k\rangle)=\top\bigr]\le\mathrm{negl}(\lambda).
$$

That is, from polynomially many copies of the state one cannot find any key whose state has large overlap with it. OWSGs are a quantum analogue of one-way functions; PRS (with $n\ge\lambda+\omega(\log\lambda)$) imply OWSGs, and mixed-state variants are also studied.

## Depends on

- [Pseudorandom quantum state generators](../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Sources

- Tomoyuki Morimae, Takashi Yamakawa, "Quantum Commitments and Signatures without One-Way Functions", CRYPTO (2022), arXiv:2112.06369.
- Tomoyuki Morimae, Takashi Yamakawa, "One-Wayness in Quantum Cryptography", TQC (2024), arXiv:2210.03394.
