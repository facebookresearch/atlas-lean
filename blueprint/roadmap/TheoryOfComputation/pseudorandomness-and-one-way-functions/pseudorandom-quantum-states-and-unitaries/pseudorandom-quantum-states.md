# Pseudorandom quantum state generators

A *pseudorandom state (PRS) generator* is a quantum polynomial-time algorithm $G$ that on input a key $k\in\{0,1\}^{\lambda}$ outputs an $n(\lambda)$-qubit pure state $|\phi_k\rangle$ such that for every polynomial $t(\lambda)$ and every quantum polynomial-time distinguisher $\mathcal{D}$,

$$
\Bigl|\Pr_{k}\bigl[\mathcal{D}(|\phi_k\rangle^{\otimes t})=1\bigr]-\Pr_{|\psi\rangle\sim\mu}\bigl[\mathcal{D}(|\psi\rangle^{\otimes t})=1\bigr]\Bigr|\le\mathrm{negl}(\lambda).
$$

*(Selectively secure) pseudorandom function-like state (PRFS)* generators (Ananth–Qian–Yuen, Definition 3.3) additionally take a classical input $x$ and output a (possibly mixed) quantum state $G_\lambda(k, x)$ such that, for any fixed (selectively chosen) polynomial-size set of distinct inputs $\{x_1, \dots, x_s\}$ and any polynomial $t(\lambda)$, no quantum polynomial-time distinguisher given $\{x_1, \dots, x_s\}$ together with $t$ copies of $G_\lambda(k, x_i)$ for each $i$ under a single uniform key $k$ can distinguish this joint state from $t$ copies of an independent Haar-random pure state $|\psi_i\rangle$ for each $x_i$ (requiring pure outputs for every key and input is the separate perfect state generation property of Definition 3.4). *Single-copy* PRS (Morimae–Yamakawa, Definition 2.2 and Remark 2.3) output pure states and require indistinguishability only for $t=1$, with no length restriction (for $n \le \lambda$ trivial basis-state constructions exist, §1.2). Complexity-theoretic lower bounds such as $\mathsf{BQP} \ne \mathsf{PP}$ apply to superlogarithmic output lengths $n(\lambda) = \omega(\log \lambda)$ (for $n(\lambda) = c\log\lambda$ with $c < 1$, statistically secure PRS exist unconditionally).

## Depends on

- [Haar-random states and t-copy indistinguishability](haar-random-states.md)
- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Zhengfeng Ji, Yi-Kai Liu, Fang Song, "Pseudorandom Quantum States", CRYPTO (2018), IACR ePrint 2018/544.
- Prabhanjan Ananth, Luowen Qian, Henry Yuen, "Cryptography from Pseudorandom Quantum States", CRYPTO (2022), arXiv:2112.10020 (Definitions 3.3 and 3.4).
- Tomoyuki Morimae, Takashi Yamakawa, "Quantum Commitments and Signatures Without One-Way Functions", CRYPTO (2022), arXiv:2112.06369 (§1.2, Definition 2.2 and Remark 2.3).
