# Pseudorandom unitaries

A *pseudorandom unitary (PRU)* family is a keyed family $\{U_k\}_{k\in\{0,1\}^{\lambda}}$ of $n$-qubit unitaries, each implementable by a quantum polynomial-time circuit given $k$, such that for every quantum polynomial-time algorithm $\mathcal{A}$ making polynomially many queries,

$$
\bigl|\Pr_k[\mathcal{A}^{U_k}=1]-\Pr_{U\sim\mathrm{Haar}}[\mathcal{A}^{U}=1]\bigr|\le\mathrm{negl}(\lambda).
$$

A PRU is *non-adaptive* if this holds for algorithms applying $U$ in parallel to a fixed state, and *strong* if it holds even with access to $U^{\dagger}$. Applying a PRU to $|0^{n}\rangle$ gives a PRS.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)

## Sources

- Zhengfeng Ji, Yi-Kai Liu, Fang Song, "Pseudorandom Quantum States", CRYPTO (2018), IACR ePrint 2018/544.
- Fermi Ma, Hsin-Yuan Huang, "How to Construct Random Unitaries", STOC (2025), IACR ePrint 2024/1652.
