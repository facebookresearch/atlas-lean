# Graph Isomorphism is in RP relative to MCSP

Graph Isomorphism has a one-sided-error randomized polynomial-time algorithm with an MCSP oracle: $\mathrm{GI}\in\mathrm{RP}^{\mathrm{MCSP}}$. The same holds with an oracle for strong nondeterministic circuit minimization or for the KT-random strings.

**Theorem (Allender–Das).** $\mathrm{GI}\in\mathrm{RP}^{\mathrm{MCSP}}$, where GI asks, for two graphs $G$ and $H$, whether some permutation $\tau$ of the vertices of $G$ satisfies $\tau(G)=H$. Moreover $\mathrm{GI}\in\mathrm{RP}^{\mathrm{SNCMP}}\cap\mathrm{RP}^{R_{\mathrm{KT}}}$, where SNCMP is minimization of strong nondeterministic circuit size.

Here "one-sided" means: on non-isomorphic pairs the algorithm never accepts, and on isomorphic pairs it accepts with probability above $1/2$.

## Expansion

Let $f_G(\tau)=\tau(G)$, computable in time polynomial in the length of $\tau$. The oracle inverter gives a machine $N$ with $\Pr_{\tau,s}[f_G(N^{\mathrm{MCSP}}(G,f_G(\tau),s))=f_G(\tau)]\ge 1/q(n)$. On input $(G,H)$, for $100q(n)$ trials pick $\tau$, compute $\tau(G)$, run $N^{\mathrm{MCSP}}(H,\tau(G),s)$ to get $\pi$, and accept if $\pi(H)=\tau(G)$. If $G\not\cong H$ no trial can succeed. If $G\cong H$, then $\tau(G)$ and $\tau(H)$ have the same distribution, so each trial succeeds with probability at least $1/q(n)$, and a Chernoff bound gives success probability above $1/2$. Truth tables needing large strong nondeterministic circuits also need large deterministic ones, which gives the SNCMP version.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)
- [Isomorphism of graph codes](../../../fine-grained-complexity/graph-isomorphism-in-quasipolynomial-time/isomorphic.md)
- [KT complexity and the minimum KT problem MKTP](kt-complexity-and-mktp.md)

## Proof depends on

- [Dense KT-random oracles invert polynomial-time functions](kt-random-oracles-invert-polynomial-time-functions.md)

## Sources

- Eric Allender, Bireswar Das, "Zero Knowledge and Circuit Minimization", *Information and Computation* 256, 2017, https://doi.org/10.1016/j.ic.2017.04.004 (Theorem 2 and Corollary 3).
