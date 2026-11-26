# Euclidean closest-vector gap hardness with integral target

Fix an input consisting of dimension $n>0$, a nonsingular integer $n\times n$ basis matrix $B$, an integral target $a\in\mathbb Z^n$, and a positive rational radius $r$. The lattice consists of $Bz$ for $z\in\mathbb Z^n$. The yes promise is $\|Bz-a\|_2^2\le r^2$ for some $z$; the no promise is $\|Bz-a\|_2^2>(n^{1/400} r)^2$ for every $z$. Distances and powers are real, and the integer target is stored as a rational vector with all coordinates integral. This bit-string promise problem is NP-hard under deterministic polynomial-time reductions.

## Depends on

- [Binary promise reductions for lattice and decoding problems](promise-reductions-for-lattices-and-linear-codes.md)

## Expansion

Verify encoded-promise disjointness and the integral-target, rational-radius and nonsingular-basis invariants of the reduction. Use the gap-producing reduction, not the exact-decision closest-vector NP-completeness theorem; that theorem does not force every no instance to clear this strict gap.

## Sources

- [OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 7](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)
- [Pinned source: `gapCVP400IsNPHard`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/H_GapCVP.lean#L153-L153)
