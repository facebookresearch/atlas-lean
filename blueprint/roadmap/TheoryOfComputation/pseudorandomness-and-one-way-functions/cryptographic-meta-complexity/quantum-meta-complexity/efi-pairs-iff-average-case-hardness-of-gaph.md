# Cavalar et al.: EFI pairs exist iff estimating quantum algorithmic entropy is hard from a single copy

EFI pairs exist if and only if some non-uniformly samplable family of pure states makes GapH, estimating a smoothed Gács quantum Kolmogorov complexity from one copy, hard on average; uniform families characterize single-copy pseudorandom states.

1. The following are equivalent: (a) EFI pairs exist; (b) there are a non-uniform family of efficiently samplable states $\{|\psi_k\rangle\}$ with advice of size $O(\log\lambda)$, efficiently computable $r\in[n(\lambda)]$, $\Delta=\omega(\log\lambda)$ and a universal constant $\epsilon<1/100$ such that GapH$_{\epsilon}(r,r+\Delta)$ is non-uniformly hard on average over $\{|\psi_k\rangle\}$.
2. Single-copy pseudorandom states exist if and only if there are a uniform family of efficiently samplable states $\{|\psi_k\rangle\}$, efficiently computable $r\in[n(\lambda)]$, a universal constant $\epsilon<1/100$ and $\Delta=\omega(\log\lambda)$ such that GapH$_{\epsilon}(r,r+\Delta)$ is hard over $\{|\psi_k\rangle\}$.
3. EFI pairs exist if and only if there are a non-uniform family of efficiently samplable states $\{|\psi_k\rangle\}$ with advice of size $O(\log\lambda)$, efficiently computable $r\in[n(\lambda)]$, $\Delta=\omega(\log\lambda)$ and a universal constant $\epsilon<1/100$ such that GapU$_{\epsilon}(r,r+\Delta)$ is non-uniformly hard on average over $\{|\psi_k\rangle\}$.
4. EFI pairs exist if and only if there are efficiently computable $r$, $\Delta=\omega(\log\lambda)$, $\epsilon<1/100$ and a non-uniform family of efficiently samplable states with advice size $O(\log\lambda)$ for which it is non-uniformly hard to decide, from a single copy of a uniformly sampled member, whether it lies in the span $\Pi_r$ of states of $K_{\mathrm{net}}$ complexity at most $r$ or has overlap at most $\epsilon$ with $\Pi_{r+\Delta}$.

## Expansion

If EFI exist, take a non-uniform 1PRS $\{|\phi_{k'}\rangle\}$ with stretch at least $\sqrt n$ and mix it with random computational basis states: $|\psi_{b,k',j}\rangle$ is $|\phi_{k'}\rangle$ when $b=0$ and $|j\rangle$ when $b=1$. The first half has $K_{\mathrm{net}}$ at most $n-\sqrt n+O(\log\lambda)$, hence low smoothed $H$, the second half has $H$ close to $n$, and single-copy pseudorandomness hides which half a sample came from. Conversely, without EFI no non-uniform pseudo-mixed states exist, so the mixture $\rho=\mathbb E_k|\psi_k\rangle\langle\psi_k|$, after a quantum extractor to $\ell=(n+r+\Delta/2)/2$ qubits, can be efficiently distinguished from maximally mixed by a projector $\Pi$; testing $\Pi$ on one copy separates low $H$ (mixtures of low-complexity states have low entropy) from high $H$ (approximately high min-entropy).

## Depends on

- [Gács quantum algorithmic entropy H and the single-copy problem GapH](gacs-quantum-algorithmic-entropy-and-gaph.md)
- [EFI pairs: efficient, statistically far, computationally indistinguishable states](../../microcrypt-and-quantum-one-wayness/efi-pairs.md)
- [Cavalar et al.: EFI pairs exist iff non-uniform single-copy pseudorandom states exist](efi-pairs-iff-nonuniform-single-copy-pseudorandom-states.md)

## Proof depends on

None.

## Sources

- Bruno Pasqualotto Cavalar, Boyang Chen, Andrea Coladangelo, Matthew Gray, Zihan Hu, Zhengfeng Ji and Xingjian Li, "A Meta-complexity Characterization of Minimal Quantum Cryptography", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800783; numbering from arXiv:2510.07859v1 (Theorems 1.2 and 1.3, Corollary 1.1, Theorem 7.1, Corollary 7.1, Theorems 8.1 and 9.1).
