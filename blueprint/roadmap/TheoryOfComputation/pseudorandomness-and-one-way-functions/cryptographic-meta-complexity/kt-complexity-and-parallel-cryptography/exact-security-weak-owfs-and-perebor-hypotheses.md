# Ren–Santhanam: exact security of weak one-way functions equals average-case circuit hardness of K^t

For security bounds $S(n)$ up to an $n^{\Theta(\log n)}$ factor, weak one-way functions secure against size-$S$ circuits exist iff $\mathrm{K}^t$ needs size-$S$ circuits to be computed on a $1-1/p(n)$ fraction of inputs; this motivates Perebor hypotheses that brute force is optimal for $\mathrm{K}^t$ and $\mathrm{KT}$.

Here $\mathrm{K}^t$ and $\mathrm{KT}$ are Ren–Santhanam's random-access measures, in which a description lets a universal machine decide each bit $x_i$ separately. A length-preserving $f:\{0,1\}^n\to\{0,1\}^n$ is a *weak one-way function with security $S(n)$* if there is a polynomial $p$ such that every circuit $C$ of size $S(n)$ satisfies $\Pr_{x\leftarrow U_n}[C(f(x))\in f^{-1}(f(x))]\le 1-1/p(n)$.

**Theorem.** Let $S$ be monotone with $S(n+O(\log^{2}n))\le S(n)\cdot n^{O(\log n)}$. The following are equivalent:

1. There is a weak one-way function with security $S(n)\cdot n^{\Theta(\log n)}$.
2. There are polynomials $p,t$ such that the search version of $\mathrm{K}^t$ requires size $S(n)\cdot n^{\Theta(\log n)}$ to compute on a $1-1/p(n)$ fraction of inputs.
3. For every constant $\lambda>0$ there are polynomials $p,t$ such that $\mathrm{K}^t$ requires size $S(n)\cdot n^{\Theta(\log n)}$ to $(\lambda\log n)$-approximate on a $1-1/p(n)$ fraction of inputs.

Moreover, if there is a weak one-way function with security $2^{\Omega(n)}$ computable in DLOGTIME, then there is a polynomial $p$ such that $\mathrm{KT}$ requires size $2^{\Omega(n)}$ to compute on a $1-1/p(n)$ fraction of inputs.

**Perebor hypotheses.** The *weak Perebor hypothesis for $\mathrm{K}^t$* states that for some polynomial $t(n)\ge 2n$ and absolute constant $c\ge 1$, every randomized algorithm running in time $2^{n/c}$ that attempts to compute $\mathrm{K}^t$ fails with probability at least $1/n^{c}$ over a uniformly random input; the weak Perebor hypothesis for $\mathrm{KT}$ is the same statement for $\mathrm{KT}$. The *strong Perebor hypothesis for $\mathrm{K}^t$* states that there are polynomials $t(n)\ge 2n$ and $p$ such that for every $\epsilon>0$ every probabilistic algorithm running in time $2^{(1-\epsilon)n}$ fails to compute $\mathrm{K}^t$ with probability at least $1/p(n)$. By the theorem, the non-uniform version of the weak hypothesis for $\mathrm{K}^t$ is equivalent to exponentially hard weak one-way functions against circuits, and the non-uniform strong hypothesis to weak one-way functions of hardness $2^{(1-o(1))n}$.

## Expansion

Both directions follow the Liu–Pass template with tight parameters. From a weak one-way function one builds a conditionally entropy-preserving PRG through Impagliazzo's hardcore lemma (which is why adversaries are non-uniform), hashing-based extractors and hardcore functions; extractors that extract all min-entropy need seed length $O(\log^{2}n)$, the source of the $n^{\Theta(\log n)}$ loss. Conversely, inverting the universal function that runs short descriptions solves search-$\mathrm{K}^t$ on most inputs. For $\mathrm{KT}$ the generator is first compiled into a DLOGTIME randomized encoding, which costs a constant factor in the exponent: security $2^{\alpha n}$ yields hardness $2^{\beta n}$ only for some much smaller $\beta$. The non-uniform strong hypothesis is likely false, since by Hellman and Fiat–Naor every function can be inverted in the non-uniform RAM model in time $2^{3n/4}$ with $2^{3n/4}$ advice.

## Depends on

- [Weak one-way function](../../one-way-function-transformations/weak-one-way-function.md)
- [Circuit complexity of a Boolean function and truth tables](../../../circuit-complexity/minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [Ren–Santhanam random-access Kt and K^t, parallel variants NC^1-K^t and L-K^t, and average-case hardness](parallel-kolmogorov-complexity-and-kt-average-case-hardness.md)

## Proof depends on

- [Conditionally entropy-preserving pseudorandom generators from one-way functions](../../meta-complexity-and-one-way-functions/conditionally-entropy-preserving-prgs.md)
- [Degree-3 decomposable randomized encodings of log-depth computations](../../../../ComputerScience/cryptography/public-key/obfuscation-and-witness-encryption/compact-functional-encryption-to-obfuscation/nc0-randomized-encoding.md)

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Definition 49, Theorems 50 and 51, Remark 52, Hypotheses 64 to 66, Section 5).
