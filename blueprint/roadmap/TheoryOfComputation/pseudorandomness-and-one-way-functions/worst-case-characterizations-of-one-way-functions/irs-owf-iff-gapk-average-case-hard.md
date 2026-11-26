# Ilango–Ren–Santhanam: one-way functions exist iff approximating (uncomputable) Kolmogorov complexity is hard on some samplable distribution

The following are equivalent:

1. One-way functions exist.
2. For some $s=n^{\Omega(1)}$ and $\Delta=\omega(\log n)$ there is a polynomial-time samplable $\mathcal D$ on which $\mathrm{GapK}[s,s+\Delta]$ is weakly average-case hard.
3. For every $\varepsilon>0$ there is a polynomial-time samplable $\mathcal D$ on which $\mathrm{GapK}[n^{\varepsilon},\ n-\omega(\log n)]$ is strongly average-case hard.

This holds in both the infinitely-often and almost-everywhere settings and needs no derandomization hypothesis; it is the first characterization of one-way functions by the average-case hardness of a fixed problem on an arbitrary samplable distribution. Assuming $\mathsf{E}\not\subseteq\mathsf{ioSIZE}[2^{0.01n}]$, the same equivalence holds between infinitely-often one-way functions and the infinitely-often hardness of $\mathrm{GapK}^{\tau}$ for every large enough polynomial $\tau$ (with the same parameters). With logspace-samplable distributions in item 2 and $\mathsf{NC}^0$-samplable distributions and $\mathrm{GapK}[n-n^{0.99},n-\omega(\log n)]$ in item 3, the analogous equivalence characterizes $\mathsf{NC}^0$-computable one-way functions.

## Proof sketch

Item 1 implies item 3 because a pseudorandom generator stretching $n^{\varepsilon}$ bits to $n$ bits produces strings of Kolmogorov complexity at most $n^{\varepsilon}+O(\log n)$ that are indistinguishable from uniform strings, whose complexity is at least $n-\omega(\log n)$ with overwhelming probability. Item 2 implies item 1 by the generic argument, since the classical coding theorem $K(x)\le\log(1/D(x))+O(\log n)$ holds for every samplable $D$: the one-way function is defined from the distribution while its security uses the structure of $K$.

## Depends on

- [GapMCSP[s,c], GapK[s,c] and weak versus strong average-case hardness on a distribution](gap-meta-complexity-and-weak-strong-average-case-hardness.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Ilango–Ren–Santhanam: a coding theorem plus average-case hardness of additive approximation yields one-way functions](irs-coding-theorem-plus-hardness-gives-owf.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)
- [Few strings have small complexity](../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
