# Saks–Zhou seed bound for randomized logspace

For every $L\in\mathsf{BPL}$ there is a deterministic estimation procedure, parameterized by a pair $(h,z)$ consisting of $s=\lfloor\sqrt{R}\rfloor+1$ shared Nisan hash seeds and $s$ random rounding shifts, with $R=O(\log n)$ the logarithm of the number of configurations, using $O(\log^{3/2} n)$ random bits in total, such that for every input $x$ a strict majority of the pairs $(h,z)$ yields an estimate on the correct side of $1/2$. The estimate is obtained by iterating $s$ times: raise the transition matrix to the power $2^s$ with Nisan's generator, then round entries down to $d=O(R)$ bits after subtracting the random shift.

## Proof sketch

Each Nisan-powering step approximates $M^{2^s}$ within $2^{-\Omega(d)}$ for most seeds; random-shift rounding makes the result a fixed function of the exact matrix with high probability, so the same seed can be reused across iterations; a union bound over $s$ levels and $|V|$ entries bounds the bad pairs.

## Depends on

- [Randomized logarithmic space RL and BPL](rl-and-bpl.md)
- [Saks–Zhou randomized rounding with a random shift](../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/space-bounded-pseudorandomness/saks-zhou-random-shift-rounding.md)

## Proof depends on

- [Nisan's generator for read-once branching programs](../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/nisan-generator.md)
- [Nisan's generator fools space-bounded computation](../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/nisan-generator-fools-space-bounded-computation.md)
- [The Saks–Zhou iteration with Nisan's generator](../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/space-bounded-pseudorandomness/saks-zhou-iteration-with-nisan-generator.md)

## Sources

- Michael Saks and Shiyu Zhou, "BP_HSPACE(S) ⊆ DSPACE(S^{3/2})", Journal of Computer and System Sciences 58(2), 376–403, 1999 (with $r_1=r_2=s$ there: $s$ levels of Nisan's generator and $s$ rounding steps).
- Noam Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 449–461, 1992.
