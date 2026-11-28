# Pseudorandom states from quantum-secure pseudorandom functions

Let $F_k:\{0,1\}^{n}\to\mathbb{Z}_N$ be a pseudorandom function secure against quantum adversaries with superposition access, with $N=2^{n}$ (or $N=2$ for binary phases). Then $|\phi_k\rangle=2^{-n/2}\sum_{x\in\{0,1\}^{n}}\omega_N^{F_k(x)}|x\rangle$ with $\omega_N=e^{2\pi i/N}$ is a pseudorandom state generator. Moreover, for a truly random function $f$, the $t$-copy states of the random phase ensemble are within trace distance $O(t^{2}/2^{n})$ of $t$ Haar-random copies, both for uniform phases and for binary phases $\pm 1$. In particular PRS exist if quantum-secure one-way functions exist.

## Proof sketch

Replace $F_k$ by a random function using PRF security; a polynomial-time preparation of $|\phi_k\rangle$ needs one superposition query. For random phases, the $t$-copy moment operator projected onto the subspace of tuples with distinct entries equals (a multiple of) the corresponding projection of the symmetric-subspace operator; the collision subspace has weight $O(t^{2}/2^{n})$, giving the trace distance bound. Binary phases need a slightly finer counting of collisions.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)
- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)
- [Haar-random states and t-copy indistinguishability](haar-random-states.md)

## Sources

- Zhengfeng Ji, Yi-Kai Liu, Fang Song, "Pseudorandom Quantum States", CRYPTO (2018), IACR ePrint 2018/544.
- Zvika Brakerski, Omri Shmueli, "(Pseudo) Random Quantum States with Binary Phase", TCC (2019), arXiv:1906.10611.
