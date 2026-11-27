# SZK reduces to MCSP

Every promise problem with a statistical zero-knowledge proof reduces to MCSP by a bounded-error randomized polynomial-time oracle algorithm: $\mathrm{SZK}\subseteq\mathrm{Promise\text{-}BPP}^{\mathrm{MCSP}}$.

**Theorem (Allender–Das).** For every promise problem $(Y,N)\in\mathrm{SZK}$ there is a probabilistic polynomial-time oracle Turing machine $M$ such that $x\in Y$ implies $M^{\mathrm{MCSP}}(x)$ accepts with probability at least $2/3$, and $x\in N$ implies $M^{\mathrm{MCSP}}(x)$ accepts with probability at most $1/3$; on inputs outside $Y\cup N$ the behavior of $M$ is arbitrary.

The proof uses a complete problem. *Polarized Image Intersection Density* (PIID) has as yes-instances triples $(n,D_0,D_1)$ of $m$-input circuits of size at most $n^k$ whose output distributions on uniform inputs have statistical distance at most $2^{-n}$, and as no-instances those with $\Pr_{|x|=m}[\exists y\ D_1(y)=D_0(x)]<2^{-n}$. PIID is complete for $\mathrm{NISZK}_h$ (Ben-Or and Gutfreund), which equals SZK (Chailloux, Ciocan, Kerenidis and Vadhan), and one may assume $m\ge n^{\delta}$ by padding the circuits with dummy inputs.

## Expansion

Let $F_C(x)=C(x)$. The oracle inverter gives $N$ with $\Pr_{x,s}[F_C(N^{\mathrm{MCSP}}(C,F_C(x),s))=F_C(x)]\ge 1/q(m)$. On $(n,D_0,D_1)$ run $n^{\ell}$ trials: pick $x$, set $z=D_0(x)$, obtain $y=N^{\mathrm{MCSP}}(D_1,z,s)$ and count a success when $D_1(y)=z$; accept if at least $\log n$ trials succeed. On no-instances each trial succeeds with probability below $2^{-n}$, since $z$ is rarely in the image of $D_1$. On yes-instances $D_0(x)$ and $D_1(x)$ are $2^{-n}$-close, so the inverter for $D_1$ still succeeds with probability about $1/q(m)$ on $D_0(x)$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](../../../randomized-and-quantum-complexity/interactive-proofs/statistical-zero-knowledge-structure/promise-szk-and-hvszk.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [Dense KT-random oracles invert polynomial-time functions](kt-random-oracles-invert-polynomial-time-functions.md)

## Sources

- Eric Allender, Bireswar Das, "Zero Knowledge and Circuit Minimization", *Information and Computation* 256, 2017, https://doi.org/10.1016/j.ic.2017.04.004 (Theorem 4, Section 4).
