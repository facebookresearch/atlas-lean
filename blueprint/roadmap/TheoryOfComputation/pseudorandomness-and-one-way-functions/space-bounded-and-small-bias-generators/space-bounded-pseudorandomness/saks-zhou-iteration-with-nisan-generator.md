# The Saks–Zhou iteration with Nisan's generator

(Walk realization.) A substochastic matrix $A$ over states $\iota$ whose entries are multiples of $1/|X|$ is the transition matrix of a deterministic walk on $\iota \cup \{\bot\}$ driven by uniform letters of $X$: from state $i$, $A_{ij}|X|$ letters lead to $j$ and the rest to an absorbing sink $\bot$; reading $m$ uniform letters moves $i$ to $j$ with probability $(A^m)_{ij}$.

(Iteration.) Let $h : H \times X \to X$ be pairwise independent, and for a hash-seed tuple $hs \in H^k$ let $\mathrm{N}(A, hs)$ be the matrix obtained by running the walk on the $2^k$ blocks of Nisan's generator from a uniform block. For $1 \le k$, $2^d \mid |X|$ and a substochastic $M$ with entries in $\mathbb{Z}/|X|$, if $(|\iota|+1)(2^k - 1)(|\iota|+1)/\sqrt{|X|} \le \varepsilon^2$, then for all but an $n_2(\varepsilon + |\iota|^2(2^d\varepsilon + 2^{-d}))$ fraction of pairs $(hs, z)$ with $z \in \{0,\dots,2^d-1\}^{n_2}$, the $n_2$-fold iteration $M_{t+1} = \mathrm{Snap}_d(\mathrm{N}(M_t, hs), z_t)$ satisfies $\|M_{n_2} - M^{2^{kn_2}}\|_\infty \le 2^{kn_2}|\iota|\,2^{1-d}$. With Boolean Toeplitz hashing on $2m$-bit blocks the seed has $k(6m - 1) + n_2 d$ bits.

## Proof sketch

By the hash mixing lemma and a union bound over $2^k - 1$ levels and the entries, most hash seeds make Nisan's powering approximate $A^{2^k}$ entrywise within $\varepsilon$. Rounding with a random shift then makes the rounded approximation equal to the rounded exact power except on few shifts, so the error does not compound across the $n_2$ rounds beyond the $2^{1-d}$ rounding loss per step.

## Depends on

- [Saks–Zhou randomized rounding with a random shift](saks-zhou-random-shift-rounding.md)
- [Nisan's hash mixing lemma](hash-mixing-lemma.md)
- [Toeplitz hashing is pairwise independent](../../../../ComputerScience/data-structures/hashing/limited-independence-hash-families/toeplitz-hashing.md)
- [Read-once branching program and space-bounded pseudorandom generator](../read-once-branching-programs-and-space-bounded-prgs.md)

## Sources

- M. Saks and S. Zhou, "BP_H SPACE(S) ⊆ DSPACE(S^{3/2})", Journal of Computer and System Sciences, 1999.
- N. Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica, 1992.
- E. Chattopadhyay and J.-J. Liao, "Optimal Error Pseudodistributions for Read-Once Branching Programs", 35th Computational Complexity Conference (CCC 2020), 2020.
- W. M. Hoza, "Better Pseudodistributions and Derandomization for Space-Bounded Computation", APPROX/RANDOM 2021, 2021.
