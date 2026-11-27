# Running time in a class with arbitrarily large constants cannot be verified

For every class of time bounds that contains arbitrarily large constant functions, such as $O(1)$, polynomial time or
exponential time, no algorithm decides whether a given Turing machine has running time bounded by a function of the class.

**Theorem.** Let $\mathcal{F}$ be a class of functions $\mathbb{N} \to \mathbb{R}_{\ge 0}$ that contains constant functions
with arbitrarily large values. Then both problems $\mathrm{HALT}_{\mathcal{F}}$ (multi-tape machines) and
$\mathrm{HALT}^1_{\mathcal{F}}$ (one-tape machines) of
[deciding whether a machine runs in time T(n) for some T in the class](turing-machines-running-within-a-time-bound.md)
are undecidable.

In particular, for both models the problems for the classes $O(1)$, $\mathsf{P}$, $\mathsf{EXP}$ and $O(T(n))$ with
$T(n) = \Omega(1)$ are undecidable: no algorithm decides whether a Turing machine runs in constant time.

## Depends on

- [Turing machines running within a time bound](turing-machines-running-within-a-time-bound.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Suppose a machine decides $\mathrm{HALT}_{\mathcal{F}}$ and let $F$ be the set of $T \in \mathcal{F}$ with $T(n) \ge n + 1$
for all $n$. If $F$ is empty, build from a one-tape machine $H$ a machine $\tilde{H}$ that on input $w$ simulates $|w|$
steps of $H$ on the empty input and halts at once if $H$ has halted, and otherwise makes an extra step; then $H$ halts on the
empty input iff $\tilde{H}$ runs in constant time iff $\tilde{H}$ runs in time $T(n)$ for some $T \in \mathcal{F}$, so halting
would be decidable. If $F$ is nonempty, the machine $\tilde{H}$ of the reduction for a single bound $T(n) \ge n + 1$ runs in
time $n + 1$ iff it always halts iff $H$ never halts. The one-tape case is the same with an extra $|w| \log |w|$ steps in the
first construction and a one-tape counting construction for bounds that are $\Omega(n \log n)$.

## Sources

- D. Gajser, "Verifying time complexity of Turing machines", *Theoretical Computer Science* 600:86–97, 2015, doi:[10.1016/j.tcs.2015.07.028](https://doi.org/10.1016/j.tcs.2015.07.028). Numbering of the version read, arXiv:1307.3648v2 (titled "Verifying Time Complexity of Deterministic Turing Machines"): Theorem 3.4 and Corollaries 3.5 and 3.6 (multi-tape), Theorem 4.2 and Corollaries 4.3 and 4.4 (one-tape).
