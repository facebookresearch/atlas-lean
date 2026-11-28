# Pseudorandom states in Algorithmica: a classical oracle with P = NP

There is a classical oracle relative to which $\mathsf{P}=\mathsf{NP}$ yet single-copy secure pseudorandom quantum states with output length $n(\lambda) > \lambda$ exist, for any polynomial $n(\lambda) > \lambda$ in the key length $\lambda$ (for $n \le \lambda$ single-copy security is trivial to achieve). In the language of Impagliazzo's five worlds, this places quantum cryptography based on pseudorandom states in Algorithmica in a black-box sense: such cryptography is possible even if one-way functions do not exist. The construction builds on an oracle with $\mathsf{P}=\mathsf{NP}$ but $\mathsf{BQP}\ne\mathsf{QCMA}$ based on the hardness of the $\mathrm{OR}\circ\mathrm{Forrelation}$ problem, together with pseudorandomness of a discretely-defined Forrelation variant against $\mathsf{AC}^{0}$ circuits.

## Proof sketch

The oracle provides an $\mathsf{NP}$-complete language's solutions (so $\mathsf{P}=\mathsf{NP}$ relative to it) plus a random instance of a quantum-friendly function whose phase states are pseudorandom. Breaking single-copy pseudorandomness would yield an $\mathsf{AC}^{0}$-type distinguisher for the Forrelation variant (because the $\mathsf{NP}$ oracle's power reduces to constant-depth circuits on the random oracle), contradicting the $\mathsf{AC}^{0}$ pseudorandomness result.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)
- [Impagliazzo's five worlds](../impagliazzo-s-five-worlds/impagliazzo-five-worlds.md)
- [Black-box constructions and oracle separations](../../../ComputerScience/cryptography/public-key/hardness-assumptions/black-box-constructions-and-oracle-separations.md)

## Sources

- William Kretschmer, Luowen Qian, Makrand Sinha, Avishay Tal, "Quantum Cryptography in Algorithmica", STOC (2023), arXiv:2212.00879 (Theorem 1, Definition 7 and Theorem 22).
