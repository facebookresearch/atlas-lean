# Ren–Santhanam: Levin's Kt is hard on average iff one-way functions exist

Although computing Levin's $\mathrm{Kt}$ is EXP-hard in the worst case, its bounded-error average-case hardness over uniform inputs is equivalent to the existence of one-way functions, and hence to average-case hardness of $\mathrm{K}^p$ for some polynomial $p$.

Here $\mathrm{Kt}$ and $\mathrm{K}^p$ are Ren–Santhanam's random-access measures (each bit $x_i$ is decided by $U^{d}(i,b)$, at cost $|d|+\log t$ for $\mathrm{Kt}$), and hardness on average is bounded-error hardness over the uniform distribution against probabilistic polynomial-time algorithms, exact or within an additive approximation. The following are equivalent:

1. $\mathrm{Kt}$ is bounded-error hard on average.
2. One-way functions exist.
3. For every constant $\lambda>0$, $\mathrm{Kt}$ is bounded-error hard on average to approximate within an additive factor of $\lambda\log n$.

Combined with the Liu–Pass theorem (one-way functions exist iff $\mathrm{K}^p$ is bounded-error hard on average for some polynomial $p$), this gives: $\mathrm{Kt}$ is bounded-error hard on average if and only if there is a polynomial $p$ such that $\mathrm{K}^p$ is bounded-error hard on average.

## Expansion

(1) implies (2): if every probabilistic polynomial-time algorithm errs on a $1/n^{c}$ fraction, then for all but a $1/n^{2c}$ fraction of $x$ one has $\mathrm{K}(x)\ge n-2c\log n-1$ while $\mathrm{Kt}(x)\le n+\log n+O(1)$, so optimal pairs $(d,t)$ with $|d|+\log t=\mathrm{Kt}(x)$ have $t\le O(n^{2c+1})$. The function $(\ell,k,M)\mapsto(\ell,k,\text{output of }U^{M'}\text{ run for }2^{k}\text{ steps})$, where $M'$ is the $\ell$-bit prefix of $M$, $\ell\le n+\log n$ and $k\le(2c+1)\log n$, has an output distribution that almost dominates the uniform one, so inverting it would solve search-$\mathrm{Kt}$ on most inputs; it is a weak one-way function. (2) implies (3): a conditionally entropy-preserving PRG with stretch $\gamma\log n$, computable in time $n^{c}$, has outputs of $\mathrm{Kt}$ at most $n+c\log n+O(1)$ while random strings of length $n+\gamma\log n$ have $\mathrm{Kt}$ close to their length; with $\gamma=\lambda+c+2$ an approximator distinguishes. (3) implies (1) is trivial.

## Depends on

- [Ren–Santhanam random-access Kt and K^t, parallel variants NC^1-K^t and L-K^t, and average-case hardness](parallel-kolmogorov-complexity-and-kt-average-case-hardness.md)
- [One-way functions exist](../../impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Conditionally entropy-preserving pseudorandom generators from one-way functions](../../meta-complexity-and-one-way-functions/conditionally-entropy-preserving-prgs.md)
- [Liu–Pass: one-way functions exist iff time-bounded Kolmogorov complexity is mildly hard on average](../../meta-complexity-and-one-way-functions/liu-pass-theorem.md)
- [Yao's amplification: weak one-way functions yield strong one-way functions](../../one-way-function-transformations/yao-weak-to-strong-amplification.md)

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Theorem 4, Theorem 79 and Corollary 80, Section 7.1).
