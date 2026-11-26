# Sergeev: upper bound on the partition rank of unique disjointness

For every finite set $\alpha$ with $|\alpha| = n$, the unambiguous $1$-cover number (SUM-rank) of unique disjointness satisfies

$$\mathrm{UC}^1(\mathrm{UDISJ}_\alpha) \le (n+1)^3 \binom{n}{\lfloor n/3 \rfloor} \le (n+1)^3 \Big(\frac{3}{\sqrt[3]{4}}\Big)^n,$$

and $\mathrm{UC}^1(\mathrm{UDISJ}_{[n]}) < 1.89^n$ for all sufficiently large $n$.

## Proof sketch

Partition the ground set into blocks using codes of minimum distance three (shortened binary Hamming codes): within a block pairs are separated by syndromes, and rectangles indexed by codeword classes together with row and column singleton pieces cover each disjoint pair exactly once while avoiding uniquely intersecting pairs.

## Depends on

- [Unambiguous covers, partition number and SUM-rank](unambiguous-covers-and-partition-number.md)
- [Unique disjointness](unique-disjointness.md)
- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Sources

- I. S. Sergeev, "Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix", preprint, 2026.
