# Pseudorandom quantum state generators

A *pseudorandom state (PRS) generator* is a quantum polynomial-time algorithm $G$ that on input a key $k\in\{0,1\}^{\lambda}$ outputs an $n(\lambda)$-qubit pure state $|\phi_k\rangle$ such that for every polynomial $t(\lambda)$ and every quantum polynomial-time distinguisher $\mathcal{D}$,

$$
\Bigl|\Pr_{k}\bigl[\mathcal{D}(|\phi_k\rangle^{\otimes t})=1\bigr]-\Pr_{|\psi\rangle\sim\mu}\bigl[\mathcal{D}(|\psi\rangle^{\otimes t})=1\bigr]\Bigr|\le\mathrm{negl}(\lambda).
$$

*Pseudorandom function-like state (PRFS)* generators additionally take an input $x$ and output $|\phi_{k,x}\rangle$ indistinguishable (given polynomially many copies for adaptively chosen inputs) from independent Haar-random states. *Single-copy* PRS require indistinguishability only for $t=1$ with $n>\lambda$.

## Depends on

- [Haar-random states and t-copy indistinguishability](haar-random-states.md)
- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Zhengfeng Ji, Yi-Kai Liu, Fang Song, "Pseudorandom Quantum States", CRYPTO (2018), IACR ePrint 2018/544.
- Prabhanjan Ananth, Luowen Qian, Henry Yuen, "Cryptography from Pseudorandom Quantum States", CRYPTO (2022), arXiv:2112.10020.
