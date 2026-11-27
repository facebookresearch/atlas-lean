# Verifying an Ω(n log n) time bound for one-tape machines is undecidable

For a time bound $T$ with $T(n) \ge n + 1$ for all $n$ and $T(n) = \Omega(n \log n)$, no algorithm decides whether a given
one-tape Turing machine runs in time $T(n)$.

**Theorem.** Let $T : \mathbb{N} \to \mathbb{R}_{\ge 0}$ satisfy $T(n) \ge n + 1$ for all $n \in \mathbb{N}$ and
$T(n) = \Omega(n \log n)$. Then the problem $\mathrm{HALT}^1_{T(n)}$ of
[deciding whether a one-tape Turing machine runs in time T(n)](turing-machines-running-within-a-time-bound.md) is
undecidable.

Here $T(n) = \Omega(n \log n)$ means $T(n) \ge k\, n \log n$ for some $k > 0$ and all large $n$. The growth condition
is sharp in the following sense, stated separately in the source: $\mathrm{HALT}^1_{T(n)}$ is decidable if $T(n_0) < n_0 + 1$
for some $n_0$, and it is decidable for every manageable function $T$ (a technical effectiveness condition, satisfied for
example by computable linear functions $Cn + D$) such that $n \log n / T(n)$ tends to infinity computably. By contrast, for
multi-tape machines the condition $T(n) \ge n + 1$ alone gives undecidability.

## Depends on

- [Turing machines running within a time bound](turing-machines-running-within-a-time-bound.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

From a one-tape machine $H$ the proof builds a one-tape machine $\tilde{H}$ such that $H$ does not halt on the empty input
iff $\tilde{H}$ runs in time $T(n)$ iff $\tilde{H}$ always halts. On an input of length $n \ge n_0$, $\tilde{H}$ marks a block
of $n$ cells between two end markers and from then on only sweeps the head across the whole block, so that each sweep costs
about $n$ steps. In its sweeps it thins out a row of counter symbols by a factor $C$ per sweep, which allows about
$\log_C n$ sweeps, and meanwhile simulates $H$ on the empty input one or two steps per two sweeps. If the counter runs out
before $H$ halts, $\tilde{H}$ halts, within $3 n \log_C n + 6n + 1 \le T(n)$ steps; if $H$ halts first, $\tilde{H}$ loops.
The decidable side uses Kobayashi's computable bound on the length of crossing sequences.

## Sources

- D. Gajser, "Verifying time complexity of Turing machines", *Theoretical Computer Science* 600:86–97, 2015, doi:[10.1016/j.tcs.2015.07.028](https://doi.org/10.1016/j.tcs.2015.07.028). Numbering of the version read, arXiv:1307.3648v2 (titled "Verifying Time Complexity of Deterministic Turing Machines"): Theorem 4.5 (undecidability), Lemma 4.1 (the reduction), Proposition 4.6 and Theorem 4.7 (the decidable cases).
