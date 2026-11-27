# BPL ⊆ DSPACE(log² n)

Randomized logarithmic space with two-sided bounded error is in deterministic space $O(\log^2 n)$:

$$
\mathsf{RL}\subseteq\mathsf{BPL}\subseteq\mathsf{DSPACE}(\log^2 n).
$$

## Proof sketch

Run the $\mathsf{BPL}$ machine on the output of Nisan's generator for every seed of $O(\log^2 n)$ bits, computing each needed output bit on demand in space $O(\log^2 n)$, and count the accepting seeds with an $O(\log^2 n)$-bit counter; accept iff the count exceeds half.

## Depends on

- [Randomized logarithmic space RL and BPL](rl-and-bpl.md)
- [Deterministic space classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Nisan's generator for read-once branching programs](../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/nisan-generator.md)
- [Nisan's generator fools space-bounded computation](../../../pseudorandomness-and-one-way-functions/space-bounded-and-small-bias-generators/nisan-generator-fools-space-bounded-computation.md)
- [Error reduction for RL](rl-error-reduction.md)

## Sources

- Noam Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 1992.
