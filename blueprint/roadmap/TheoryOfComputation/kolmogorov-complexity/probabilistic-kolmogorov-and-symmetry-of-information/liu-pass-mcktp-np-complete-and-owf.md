# Liu–Pass: conditional K^t (McK^tP) is NP-complete and its mild average-case hardness is equivalent to one-way functions

Programs are RAM machines. For a polynomial $\zeta$, let $\mathrm{McK^tP}[\zeta]$ be the set of triples $(x,z,k)$ with $|z|=\zeta(|x|)$, $|k|=\log|x|$ and $K^t(x\mid z)<k$, where $K^t(x\mid z)$ is the length of a shortest program that, given auxiliary input $z$, outputs $x$ within $t(|x|)$ steps. Then:

1. for every polynomial $t(n)\ge n^2$ there is a polynomial $\zeta$ such that $\mathrm{McK^tP}[\zeta]$ is $\mathsf{NP}$-complete;
2. for every polynomial $t(n)\ge 1.1n$ and every polynomial $\zeta$, mild average-case hardness of $\mathrm{McK^tP}[\zeta]$ over uniformly random instances (no probabilistic polynomial-time algorithm succeeds on a $1-1/p(n)$ fraction for some polynomial $p$) is equivalent to the existence of one-way functions.

Consequently there are concrete polynomials $t,\zeta$ such that basing one-way functions on $\mathsf{NP}\not\subseteq\mathsf{BPP}$ is equivalent to a worst-case to mild-average-case reduction for the single $\mathsf{NP}$-complete problem $\mathrm{McK^tP}[\zeta]$; this is the first natural $\mathsf{NP}$-complete problem whose uniform average-case hardness characterizes one-way functions.

## Proof sketch

For NP-completeness, the auxiliary input $z$ is used to obfuscate a hard instance: a reduction from an NP-complete problem embeds the instance into $z$ so that $x$ has a short conditional description exactly when a witness exists, with the time bound $t\ge n^2$ leaving room to verify it. For item 2, the Liu–Pass argument for unconditional $K^t$ carries over: a one-way function yields a pseudorandom generator whose outputs have low conditional complexity yet look random, so a heuristic for $\mathrm{McK^tP}$ would break it; conversely, if one-way functions do not exist, inverting the function that maps a program and its length to its time-bounded output on $z$ computes $K^t(x\mid z)$ on most uniformly random instances.

## Depends on

- [One-way functions exist](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Polynomial-time symmetry of information hypothesis for K^t and pK^t](polynomial-time-symmetry-of-information-hypothesis.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- Yanyi Liu and Rafael Pass, "On One-Way Functions from NP-Complete Problems", CCC (2022).
