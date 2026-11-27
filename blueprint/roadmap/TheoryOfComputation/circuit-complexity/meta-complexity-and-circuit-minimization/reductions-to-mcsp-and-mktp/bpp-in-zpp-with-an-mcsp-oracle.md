# BPP is contained in ZPP relative to MCSP

With an MCSP oracle, two-sided-error randomized polynomial time collapses to zero error: $\mathrm{BPP}\subseteq\mathrm{ZPP}^{\mathrm{MCSP}}$. Consequently, if MCSP is in P then $\mathrm{BPP}\subseteq\mathrm{ZPP}$.

**Theorem (Kabanets–Cai).** $\mathrm{BPP}\subseteq\mathrm{ZPP}^{\mathrm{MCSP}}$, where MCSP takes the truth table of an $n$-variable Boolean function (of length $2^n$) and a size bound in binary. In particular, if $\mathrm{MCSP}\in\mathrm{P}$ then $\mathrm{BPP}\subseteq\mathrm{ZPP}$.

The inclusion would follow at once from $\mathrm{BPP}\subseteq\mathrm{ZPP}^{\mathrm{NP}}$ if MCSP were known to be NP-hard; the theorem needs no such hardness.

## Expansion

Given a BPP machine and an input of length $n$, guess a random truth table on $O(\log n)$ variables and ask the MCSP oracle whether it has circuits of size $n^{\Omega(1)}$; output "don't know" if it does. Since most Boolean functions are hard, a hard function is found with high probability. The Impagliazzo–Wigderson generator built from that hard function has logarithmic seed and fools the machine, so enumerating all seeds simulates it deterministically with no error.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)
- [Pseudorandom generators with logarithmic seed derandomize BPP](../../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-with-logarithmic-seed.md)

## Sources

- Valentine Kabanets, Jin-Yi Cai, "Circuit Minimization Problem", *Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC)*, 2000, https://doi.org/10.1145/335305.335314 (Theorem 12 and Corollary 13 of the full version read).
