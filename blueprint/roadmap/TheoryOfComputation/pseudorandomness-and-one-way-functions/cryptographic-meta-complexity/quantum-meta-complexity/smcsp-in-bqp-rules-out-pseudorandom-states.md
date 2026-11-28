# Chia–Chou–Zhang–Zhang: SMCSP in BQP rules out pseudorandom quantum states

If the state minimum circuit size problem SMCSP is in BQP, then pseudorandom quantum states, and hence quantum-secure one-way functions, do not exist.

A family $\{|\psi_k\rangle\}_{k\in K}$ is pseudorandom if a quantum polynomial-time algorithm prepares $|\psi_k\rangle$ from $k$, and for every quantum polynomial-time $A$ and every $m=\mathrm{poly}(\kappa)$ the probabilities that $A$ accepts $m$ copies of $|\psi_k\rangle$ (random $k$) and $m$ copies of a Haar-random state differ by $\mathrm{negl}(\kappa)$.

Quantum-secure one-way functions are polynomial-time computable functions that no quantum polynomial-time algorithm inverts with non-negligible probability.

**Theorem.** If SMCSP $\in$ BQP, then there is no pseudorandom state family and no quantum-secure one-way function.

## Expansion

The adversary knows the generation algorithm, hence a size bound $s$ for circuits preparing $|\psi_k\rangle$, though not the key. Running an SMCSP algorithm with size parameter $s$ on $\mathrm{poly}(s)$ copies accepts pseudorandom states, while a Haar-random $n$-qubit state has circuit complexity exponential in $n$ with high probability and is rejected. Since quantum-secure one-way functions yield pseudorandom states (Ji–Liu–Song), breaking every pseudorandom state family also inverts every quantum-secure one-way function.

## Depends on

- [State and unitary minimum circuit size problems SMCSP and UMCSP](state-and-unitary-minimum-circuit-size-problems.md)
- [Pseudorandom quantum state generators](../../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)
- [Haar-random states and t-copy indistinguishability](../../pseudorandom-quantum-states-and-unitaries/haar-random-states.md)
- [Negligible functions](../../../complexity-classes/time-and-space-complexity-classes/negligible.md)
- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)
- [Chia–Chou–Zhang–Zhang: MQCSP in BQP rules out quantum-secure one-way functions](mqcsp-in-bqp-rules-out-quantum-secure-one-way-functions.md)

## Proof depends on

- [Pseudorandom states from quantum-secure pseudorandom functions](../../pseudorandom-quantum-states-and-unitaries/random-phase-prs.md)

## Sources

- Nai-Hui Chia, Chi-Ning Chou, Jiayu Zhang and Ruizhe Zhang, "Quantum Meets the Minimum Circuit Size Problem", *13th Innovations in Theoretical Computer Science Conference (ITCS 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.ITCS.2022.47; numbering from arXiv:2108.03171v3 (Definition 5.29, Theorem 5.30).
