# Kt and rKt are linearly related iff exponential-time derandomization holds (up to advice)

Randomized decoding gives at most a constant-factor saving over Levin's Kt for every string exactly when randomized exponential time can be derandomized, up to linear advice; in particular the two measures are linearly related if E requires exponential-size circuits. If MKtP is in P, randomness saves exponentially on some strings.

1. If $\text{Promise-BPE}\subseteq\text{Promise-E}$, then $\mathrm{Kt}(w)=O(\mathrm{rKt}(w))$ for every string $w$.
2. If $\mathrm{Kt}(w)=O(\mathrm{rKt}(w))$ for every string $w$, then $\mathrm{BPE}\subseteq\mathrm{E}/O(n)$.
3. If $\mathrm{MKtP}\in\mathrm{P}$, there is a sequence $\{w_n\}_{n\ge1}$ with $w_n\in\{0,1\}^n$, $\mathrm{rKt}(w_n)=O(\log n)$ and $\mathrm{Kt}(w_n)=\Omega(n)$.

Under the derandomization hypothesis of item 1, MrKtP and MKtP essentially coincide, so the unconditional hardness of MrKtP is evidence that MKtP is hard.

## Expansion

For item 1, consider the promise problem whose instances $(M',t',1^{c\log t'},i)$ ask whether the $i$-th output bit of the randomized machine $M'$ run for $t'$ steps is $1$ (or $0$) with probability at least $2/3$; it lies in Promise-BPE. A deterministic $2^{O(m)}$-time algorithm for it, run for $i=1,\dots,n$ on the pair $(M,t)$ witnessing $\mathrm{rKt}(w)$, prints $w$, giving $\mathrm{Kt}(w)=O(|M|+\log t+\log n)=O(\mathrm{rKt}(w))$ since $\mathrm{rKt}(w)\ge\log|w|$. For item 2, the string $w_n$ listing the values of a BPE language on all inputs of length at most $n$ has $\mathrm{rKt}(w_n)=O(n)$, hence $\mathrm{Kt}(w_n)=O(n)$, and the corresponding deterministic machines serve as linear advice. If E requires exponential-size circuits, logarithmic-seed generators derandomize Promise-BPTIME, which gives the linear relation. For item 3, $\mathrm{MKtP}\in\mathrm{P}$ implies $\mathrm{PSPACE}\subseteq\mathrm{ZPP}$, so circuit satisfiability is solvable in randomized polynomial time, and self-reduction finds the lexicographically first string of length $n$ rejected by a circuit for $\mathrm{MKtP}$ with threshold $n/2$.

## Depends on

- [Randomized Levin complexity rKt and the problem MrKtP](randomized-levin-complexity-rkt.md)
- [The minimum Kt problem MKtP](../../time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)

## Proof depends on

- [Pseudorandom generators with logarithmic seed derandomize BPP](../../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-with-logarithmic-seed.md)

## Sources

- Igor Carboni Oliveira, "Randomness and Intractability in Kolmogorov Complexity", *46th International Colloquium on Automata, Languages, and Programming (ICALP 2019)*, LIPIcs 132, 2019, [doi:10.4230/LIPIcs.ICALP.2019.32](https://doi.org/10.4230/LIPIcs.ICALP.2019.32) (Theorems 4 and 5, Theorems 24 and 25 in Section 5).
