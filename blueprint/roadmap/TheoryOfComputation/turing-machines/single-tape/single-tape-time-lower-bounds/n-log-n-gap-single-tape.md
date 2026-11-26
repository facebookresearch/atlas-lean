# Hennie–Trakhtenbrot–Kobayashi: single-tape machines in time o(n log n) decide only regular languages

If a deterministic single-tape Turing machine with state set $Q$ decides a language $L$ within time $T(n)\le\frac{n\lfloor\log_2n\rfloor}{8d}$ for all large $n$, where $d=\lceil\log_2(|Q|+2)\rceil$, then $L$ is regular. In particular, every language decided by a single-tape machine in time $o(n\log n)$ is regular, and the bound is tight (e.g. $\{0^k1^k\}$ is decidable in time $O(n\log n)$).

## Proof sketch

If some crossing sequence were long, take a shortest input forcing a crossing sequence of length $\ge h$; using cut and paste one can remove segments between boundaries with equal crossing sequences, contradicting minimality unless the total time is $\Omega(n\log n)$. Hence all crossing sequences are bounded by a constant, and a machine with bounded crossing sequences is simulated by a two-way, hence one-way, finite automaton.

## Depends on

- [Crossing sequences of single-tape Turing machines](crossing-sequences.md)

## Proof depends on

- [Fooling sets give single-tape time lower bounds; palindromes need quadratic time](single-tape-quadratic-lower-bounds.md)

## Sources

- F. C. Hennie, "One-tape, off-line Turing machine computations", Information and Control 8(6), 1965.
- Kojiro Kobayashi, "On proving time constructibility of functions", Theoretical Computer Science 35, 1985.
