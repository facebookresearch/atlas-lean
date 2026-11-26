# Targeted pseudorandom generators and targeted hitting-set generators

A **targeted pseudorandom generator** for time $t(n)$ with error $\varepsilon$ is a deterministic algorithm $G$ that, given an input (the *target*) $x\in\{0,1\}^n$ and $1^m$, prints a multiset $S_x\subseteq\{0,1\}^m$ such that for every probabilistic (or deterministic) uniform algorithm $D$ running in time $t(n)$ and all sufficiently large $x$,

$$
\Bigl|\Pr_{r\in\{0,1\}^m}[D(x,r)=1]-\Pr_{s\in S_x}[D(x,s)=1]\Bigr|\le\varepsilon .
$$

The distinguisher receives the **same** target $x$ as the generator, so it is a uniform machine with access to $x$ rather than a non-uniform circuit. A **targeted hitting-set generator** only requires: if $\Pr_r[D(x,r)=1]\ge 1/2$ then $D(x,s)=1$ for some $s\in S_x$. The generator is efficient if $S_x$ is printed in time $\mathrm{poly}(n,m)$.

Enumerating $S_x$ and evaluating a probabilistic algorithm on input $x$ with each $s\in S_x$ as its random string derandomizes it on $x$: an efficient targeted hitting-set generator for $t(n)=n^{c}$ ($c$ large) gives $\mathrm{prRP}=\mathrm{prP}$, and an efficient targeted PRG gives $\mathrm{prBPP}=\mathrm{prP}$, by taking $x$ to be the instance of the $\mathrm{prBPP}$-complete Circuit Acceptance Probability Problem (CAPP).

## Depends on

- [Pseudorandom generators against circuits](../derandomization/pseudorandom-generators-against-circuits.md)
- [Polynomial-time reduction between promise problems](../../randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)

## Sources

- Oded Goldreich, "In a World of P=BPP", Studies in Complexity and Cryptography, LNCS 6650 (2011).
- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
