# Gács quantum algorithmic entropy H and the single-copy problem GapH

Gács-style complexity of an $n$-qubit pure state is $H(|\psi\rangle)=-\log\langle\psi|\mu_n|\psi\rangle$ for a universal semi-density matrix $\mu_n$; GapH asks, from a single copy, whether a smoothed version is at most $r$ or $H$ is at least $r+\Delta$.

Fix a universal prefix-free Turing machine $U$ and a finite universal gate set $B$. Let $\mu_n$ be the universal semi-density matrix obtained by running $U$ on a uniformly random program and, when it outputs a circuit $C$ over $B$ producing an $n$-qubit state, taking the state $C|0\rangle$. Then

$$
H(|\psi\rangle)=-\log\langle\psi|\mu_n|\psi\rangle ,\qquad H_{\epsilon}(|\psi\rangle)=\max_{|\phi\rangle:\,D(|\psi\rangle,|\phi\rangle)\le\epsilon}H(|\phi\rangle),
$$

with $D$ the trace distance. The related $K_{\mathrm{net}}^{\epsilon}(|\psi\rangle)$ (Mora–Briegel) is the least $|p|$ such that $U(p)$ outputs a circuit $C$ with $|\langle\psi|C|0^{m}\rangle|^{2}\ge 1-\epsilon$, and $U(|\psi\rangle)=D_{\infty}(|\psi\rangle\langle\psi|\,\|\,\mu)=\log\langle\psi|\mu^{-1}|\psi\rangle$ is the relative min-entropy with respect to $\mu$; always $U(|\psi\rangle)\le K_{\mathrm{net}}(|\psi\rangle)$. Its smoothed version is $U_{\epsilon}(|\psi\rangle)=\min_{|\phi\rangle:\,D(|\psi\rangle,|\phi\rangle)\le\epsilon}U(|\phi\rangle)$; unlike $H_{\epsilon}$, this smoothing takes a minimum.

**GapH$_{\epsilon}(r,r+\Delta)$:** given a single copy of an $n$-qubit state $|\psi\rangle$, decide whether $H_{1-\epsilon}(|\psi\rangle)\le r$ or $H(|\psi\rangle)\ge r+\Delta$. For functions $r,\Delta,n$ of $\lambda$, GapH$_{\epsilon}(r,r+\Delta)$ is **hard over a keyed family** $\{|\psi_k\rangle:k\in\{0,1\}^{n(\lambda)}\}$ if each case occurs with probability at least $1/2-\mathrm{negl}(\lambda)$ over $k$, and every quantum polynomial-time $A$ has $|\Pr_k[A(1^{\lambda},|\psi_k\rangle)=0\mid C_{\mathrm{high}}]-\Pr_k[A(1^{\lambda},|\psi_k\rangle)=0\mid C_{\mathrm{low}}]|\le\mathrm{negl}(\lambda)$, where $C_{\mathrm{high}},C_{\mathrm{low}}$ are the two cases; it is non-uniformly hard if this holds against non-uniform quantum polynomial-time adversaries. GapU is defined in the same way with $U(|\psi\rangle)\le r$ versus $U_{1-\epsilon}(|\psi\rangle)\ge r+\Delta$.

## Expansion

The smoothing of $H$ takes a maximum, as for smoothed min-entropies: every state is $2^{-\log^{2}n}$-close to a state with $H$ below $2\log^{2}n+\log(cn)$, so for $H_{\epsilon}$ only the maximum is meaningful (whereas $U_{\epsilon}$ takes a minimum). $H$ and $U$ sandwich each other under smoothing: $U_{1-\epsilon}(|\psi\rangle)\ge H(|\psi\rangle)+\log\epsilon$ and $H_{1-\epsilon}(|\psi\rangle)\le U(|\psi\rangle)-\log\epsilon$. These measures are invariant up to small additive terms under changing $U$ and $B$, and on classical strings they reduce to time-unbounded Kolmogorov complexity.

## Depends on

- [Kolmogorov complexity](../../../kolmogorov-complexity/k.md)
- [Universal gate set](../../../../QuantumInformation/quantum-error-correction/universal-gate-sets/universal-gate-set.md)
- [Trace norm and trace distance](../../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/trace-norm-and-trace-distance.md)
- [Negligible functions](../../../complexity-classes/time-and-space-complexity-classes/negligible.md)
- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Proof depends on

None.

## Sources

- Bruno Pasqualotto Cavalar, Boyang Chen, Andrea Coladangelo, Matthew Gray, Zihan Hu, Zhengfeng Ji and Xingjian Li, "A Meta-complexity Characterization of Minimal Quantum Cryptography", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800783; numbering from arXiv:2510.07859v1 (Definitions 3.2, 3.11 to 3.16, Lemmas 3.7 to 3.10, Appendix A).
