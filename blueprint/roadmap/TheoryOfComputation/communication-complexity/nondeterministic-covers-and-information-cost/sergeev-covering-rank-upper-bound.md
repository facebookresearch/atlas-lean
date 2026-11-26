# Sergeev: the Kaibel–Weltge bound is tight up to a polynomial factor

For every finite set $\alpha$ with $|\alpha| = n \ge 1$,

$$C^1(\mathrm{UDISJ}_\alpha) \le 8 (n+1)^7 \Big(\frac{3}{2}\Big)^n.$$

Together with the Kaibel–Weltge lower bound, $(3/2)^n \le C^1(\mathrm{UDISJ}_{[n]}) \le 1024\, n^7 (3/2)^n$ for every $n \ge 1$.

## Proof sketch

A greedy covering lemma (in the style of Lovász and Stein) applied to a uniform family of rectangles built from shortened Hamming-code partitions covers all $3^n$ disjoint pairs with an overhead logarithmic in their number; careful integer rounding of the parameters and binomial mode estimates keep the bound explicit for every $n$.

## Depends on

- [Unique disjointness](unique-disjointness.md)
- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)

## Proof depends on

- [Kaibel–Weltge: unique disjointness needs (3/2)^n rectangles](kaibel-weltge-unique-disjointness-cover-bound.md)

## Sources

- I. S. Sergeev, "Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix", preprint, 2026.
- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
