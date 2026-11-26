# From pseudorandom states with logarithmic output length to classical pseudorandom strings

Pseudorandom quantum states with output length $n=O(\log\lambda)$ qubits (PRS on few qubits, also called short PRS) imply quantum pseudorandom *generators* (QPRGs): quantum polynomial-time algorithms $G$ mapping a key $k \in \{0,1\}^{\lambda}$ to classical strings that are $(1-1/\mathrm{poly}(\lambda))$-pseudodeterministic (for all but a $1/\mathrm{poly}(\lambda)$ fraction of keys, $G(k)$ is one fixed string with probability at least $1 - 1/\mathrm{poly}(\lambda)$) and pseudorandom ($G(k)$ for uniform $k$ is computationally indistinguishable from a uniform string). Such QPRGs give statistically binding, computationally hiding quantum commitments and pseudo one-time pads.

## Proof sketch

With logarithmically many qubits, polynomially many copies of $|\phi_k\rangle$ determine its measurement statistics to inverse-polynomial accuracy, and the key step is a procedure that, from such copies, pseudodeterministically extracts a string that is close to uniform when the state is Haar random; pseudorandomness of the PRS then transfers to the extracted strings.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)

## Sources

- Prabhanjan Ananth, Yao-Ting Lin, Henry Yuen, "Pseudorandom Strings from Pseudorandom Quantum States", ITCS (2024), IACR ePrint 2023/904.
