# The Microcrypt hierarchy of quantum primitives below one-way functions

The following implications hold among quantum cryptographic primitives (black-box): quantum-secure one-way functions $\Rightarrow$ pseudorandom unitaries $\Rightarrow$ pseudorandom function-like states $\Rightarrow$ pseudorandom states (with long outputs) $\Rightarrow$ one-way state generators $\Rightarrow$ one-way puzzles $\Rightarrow$ EFI pairs $\Leftrightarrow$ quantum commitments $\Leftrightarrow$ quantum oblivious transfer. In the other direction, there are oracle separations: pseudorandom states (single-copy) exist relative to a classical oracle with $\mathsf{P}=\mathsf{NP}$ (so they do not imply one-way functions), and pseudorandom states exist relative to a quantum oracle with $\mathsf{BQP}=\mathsf{QMA}$. Pseudorandom states with superlogarithmic output length $n(\lambda) = \omega(\log \lambda)$ qubits imply that $\mathsf{BQP}\ne\mathsf{PP}$ (Kretschmer, Theorem 27), so these Microcrypt primitives still require some complexity-theoretic hardness.

## Proof sketch

Each forward implication is one of the constructions above: PFC-based PRUs from one-way functions, PRU applied to inputs yields PRFS, PRS imply OWSG by a rank argument, OWSG imply one-way puzzles by shadow tomography, one-way puzzles imply EFI, and EFI is equivalent to commitments and OT. The separations are the oracle theorems of Kretschmer and of Kretschmer–Qian–Sinha–Tal, and the necessity of $\mathsf{BQP}\ne\mathsf{PP}$ is Kretschmer's breaking algorithm.

## Depends on

- [EFI pairs: efficient, statistically far, computationally indistinguishable states](efi-pairs.md)
- [One-way puzzles](one-way-puzzles.md)
- [One-way state generators](one-way-state-generators.md)
- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)
- [Pseudorandom unitaries](../pseudorandom-quantum-states-and-unitaries/pseudorandom-unitaries.md)
- [Pseudorandom quantum state generators](../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)
- [Black-box constructions and oracle separations](../../../ComputerScience/cryptography/public-key/hardness-assumptions/black-box-constructions-and-oracle-separations.md)
- [QMA for promise problems](../../randomized-and-quantum-complexity/local-hamiltonian-problem/qmapromise.md)

## Proof depends on

- [Quantum commitments and secure computation from one-way state generators](commitments-from-quantum-one-wayness.md)
- [Pseudorandom unitaries from the PFC ensemble and one-way functions](../pseudorandom-quantum-states-and-unitaries/pfc-ensemble-pru.md)
- [Pseudorandom states in Algorithmica: a classical oracle with P = NP](../pseudorandom-quantum-states-and-unitaries/prs-in-algorithmica.md)
- [Pseudorandom states can exist even if BQP = QMA](../pseudorandom-quantum-states-and-unitaries/prs-vs-bqp-qma.md)
- [Quantum commitments from pseudorandom states](prs-imply-commitments.md)
- [Pseudorandom states with long outputs are one-way state generators](prs-imply-owsg.md)
- [Minicrypt](../impagliazzo-s-five-worlds/minicrypt.md)

## Sources

- Tomoyuki Morimae, Takashi Yamakawa, "One-Wayness in Quantum Cryptography", TQC (2024), arXiv:2210.03394.
- Dakshita Khurana, Kabir Tomer, "Commitments from Quantum One-Wayness", STOC (2024), arXiv:2310.11526.
- William Kretschmer, Luowen Qian, Makrand Sinha, Avishay Tal, "Quantum Cryptography in Algorithmica", STOC (2023), arXiv:2212.00879.
- William Kretschmer, "Quantum Pseudorandomness and Classical Complexity", TQC (2021), arXiv:2103.09320.
- Zvika Brakerski, Ran Canetti, Luowen Qian, "On the Computational Hardness Needed for Quantum Cryptography", ITCS (2023), arXiv:2209.04101.
