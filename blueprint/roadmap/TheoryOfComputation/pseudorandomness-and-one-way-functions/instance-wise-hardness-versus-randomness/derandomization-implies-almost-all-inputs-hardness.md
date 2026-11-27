# Chen–Tell: prBPP = prP forces polynomial-time functions hard on almost all inputs

If $\mathrm{prBPP}=\mathrm{prP}$, then for every $c\in\mathbb{N}$ there is a function $f\colon\{0,1\}^n\to\{0,1\}^n$ computable in deterministic polynomial time such that $f$ cannot be computed in probabilistic time $n^{c}$ on almost all inputs (in the sense of the almost-all-inputs definition).

## Proof sketch

Enumerate probabilistic machines $M_1,M_2,\dots$ with clock $n^c$. On input $x$ of length $n$, the $i$-th output bit of $f(x)$ (for $i\le n$) is chosen to differ from the most likely $i$-th output bit of $M_i(x)$. Deciding the most likely bit is a $\mathrm{prBPP}$ problem (with a gap after amplification), so by the hypothesis it is done deterministically in time $n^{O(c)}$. Any fixed machine $M_i$ is diagonalized on every input of length $n\ge i$, so it fails on almost all inputs.

## Depends on

- [Hardness of a multi-output function on almost all inputs for probabilistic time](almost-all-inputs-hardness.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../../hierarchy-theorems-and-barriers/time-hierarchy-theorem/time-hierarchy.md)

## Sources

- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
