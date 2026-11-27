# Allender–Cheraghchi–Myrisiotis–Tirumala–Volkovich: McKTP is hard on average iff logspace one-way functions exist

McKTP is $1/p$-hard on average over uniform instances for some polynomial $p$ if and only if one-way functions computable in logarithmic space exist, tying an NP-complete problem to parallel cryptography.

1. If for some $m:\mathbb{N}\to\mathbb{N}$ the problem McK$^m$TP of dimension $n$ is $(1/p)$-hard on average for some polynomial $p$, then there is a weak one-way function computable in logspace, and hence a one-way function computable in logspace (in particular a one-way function).
2. If logspace-computable one-way functions exist, then McKTP is hard on average on a polynomial fraction of its instances.
3. Consequently, McKTP is hard on average if and only if logspace-computable one-way functions exist.

The authors also show (in the full version) that polynomial-time one-way functions imply that McKTP is hard on average on an exponentially small fraction of its instances. Since McKTP is NP-complete under randomized reductions, an average-case NP-hardness proof for it would exclude Pessiland.

## Expansion

For item 1, consider $f(s,t,y,\Pi')=(s+t,\ U^{\Pi,y}(1,1^{t}),\dots,U^{\Pi,y}(n,1^{t}),\ y)$, where $\Pi$ is the $s$-bit prefix of $\Pi'\in\{0,1\}^{n+c\log n}$ and $t\le d\log n$. It is computable in logspace, and for every $y$ most $x$ have an optimal pair with $t=O(\log n)$, so an inverter for $f$ solves the search problem on most instances; as in Ren–Santhanam's argument for KT, $f$ is a weak one-way function, and Yao amplification preserves logspace computability. For item 2, the Ren–Santhanam proof that logspace one-way functions make KT hard to approximate carries over: pseudorandom outputs have small conditional KT given $y$, random strings do not.

## Depends on

- [Conditional KT complexity and the Minimum Conditional KT Problem McKTP](conditional-kt-complexity-and-mcktp.md)
- [One-way function families](../../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Weak one-way function](../../one-way-function-transformations/weak-one-way-function.md)

## Proof depends on

- [Ren–Santhanam: KT is hard on average iff one-way functions exist in NC0](kt-hardness-characterizes-nc0-one-way-functions.md)
- [Yao's amplification: weak one-way functions yield strong one-way functions](../../one-way-function-transformations/yao-weak-to-strong-amplification.md)

## Sources

- Eric Allender, Mahdi Cheraghchi, Dimitrios Myrisiotis, Harsha Tirumala and Ilya Volkovich, "One-Way Functions and a Conditional Variant of MKTP", *41st IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.FSTTCS.2021.7 (Theorems 1, 3, 4 and 5, Corollary 6, Theorems 15 and 18, Corollary 19, Theorem 22, Corollary 23, Section 5).
