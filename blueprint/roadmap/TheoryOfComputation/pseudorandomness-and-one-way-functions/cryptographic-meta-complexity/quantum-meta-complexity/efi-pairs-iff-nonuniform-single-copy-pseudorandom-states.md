# Cavalar et al.: EFI pairs exist iff non-uniform single-copy pseudorandom states exist

EFI pairs, the minimal primitive of quantum cryptography, exist if and only if there are single-copy pseudorandom state generators that are non-uniform with $O(\log\lambda)$ bits of advice.

A family $\{|\phi_k\rangle\}$ of $n(\lambda)$-qubit states with key length $\ell(\lambda)<n(\lambda)$ is a **single-copy pseudorandom state (1PRS)** family if a quantum polynomial-time algorithm prepares $|\phi_k\rangle$ from $(1^{\lambda},k)$ and every quantum polynomial-time $A$ satisfies $|\Pr_k[A(1^{\lambda},|\phi_k\rangle)=1]-\Pr_{|\phi\rangle\leftarrow\mu_n}[A(1^{\lambda},|\phi\rangle)=1]|=\mathrm{negl}(\lambda)$, with $\mu_n$ the Haar measure. In a *non-uniform* 1PRS the preparation algorithm is non-uniform quantum polynomial time with an advice string $a$, of length the advice size.

**Theorem.** EFI pairs exist if and only if non-uniform 1PRS with advice size $O(\log\lambda)$ exist. Moreover, if EFI pairs exist then there is such a non-uniform 1PRS of $n(\lambda)$ qubits whose stretch is at least $\sqrt{n(\lambda)}$.

As a corollary there is an explicit universal EFI construction: EFI exist iff, for some efficiently computable $T,n=\mathrm{poly}(\lambda)$ and $r=n-\omega(\log n)$, the pair consisting of the uniform mixture $\rho^{T}_r$ of the outputs of all programs of length at most $r$ run for time $T$ and the maximally mixed state $2^{-n}I$ is an $(\epsilon,\delta)$-weak EFI with $\epsilon=\mathrm{negl}(\lambda)$ and $\delta=1-\Omega(1/\lambda)$.

## Expansion

1PRS imply EFI pairs, and the non-uniformity is harmless for that direction. For the converse, EFI pairs give entropic EFI pairs (statistical distance replaced by an entropy gap), which give non-uniform pseudo-mixed states: efficiently preparable $n$-qubit mixed states of von Neumann entropy below $n-1/\mathrm{poly}(\lambda)$ that are computationally indistinguishable from the maximally mixed state; the $O(\log\lambda)$ bits of advice record the entropy of one side of the entropic EFI pair to the needed precision. A quantum strong extractor built from unitary 2-designs and the decoupling theorem then turns a pseudo-mixed state into single-copy pseudorandom pure states. Parallel repetition boosts the stretch.

## Depends on

- [EFI pairs: efficient, statistically far, computationally indistinguishable states](../../microcrypt-and-quantum-one-wayness/efi-pairs.md)
- [Haar-random states and t-copy indistinguishability](../../pseudorandom-quantum-states-and-unitaries/haar-random-states.md)

## Proof depends on

- [Pseudorandom quantum state generators](../../pseudorandom-quantum-states-and-unitaries/pseudorandom-quantum-states.md)

## Sources

- Bruno Pasqualotto Cavalar, Boyang Chen, Andrea Coladangelo, Matthew Gray, Zihan Hu, Zhengfeng Ji and Xingjian Li, "A Meta-complexity Characterization of Minimal Quantum Cryptography", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800783; numbering from arXiv:2510.07859v1 (Definitions 3.4, 3.5 and 3.6, Theorems 1.1, 3.1, 4.1, 4.2, 5.2, 5.3, Corollary 5.1, Theorem 6.1).
