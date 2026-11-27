# Real RAM, the Real 3SUM hypothesis and the Real APSP hypothesis

The **Real RAM** stores real numbers in unit-cost registers and supports exact comparisons and arithmetic operations on them, together with an integer word RAM for indices; a **reasonable** Real RAM restricts which operations may be applied to reals (e.g. forbidding floor and bit extraction of real values) so that it cannot exploit unbounded precision. Recall the integer 3SUM and APSP hypotheses on the word RAM. Their real-valued versions are:

- **Real 3SUM hypothesis**: for every $\varepsilon > 0$ there is no $O(n^{2-\varepsilon})$-time algorithm, on a reasonable Real RAM, that decides whether $n$ given real numbers contain $a,b,c$ with $a+b+c=0$.
- **Real APSP hypothesis**: for every $\varepsilon > 0$ there is no $O(n^{3-\varepsilon})$-time algorithm, on a reasonable Real RAM, for all-pairs shortest paths in $n$-vertex directed graphs with real edge weights (and no negative cycles).

These are stated as hypotheses. They are weaker assumptions (more believable) than their integer counterparts, since integer inputs are a special case and integer algorithms may use hashing and bit tricks unavailable to real inputs; Real APSP can be solved in $n^3/2^{\Omega(\sqrt{\log n})}$ time.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [The word-RAM model](../fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Timothy M. Chan, Virginia Vassilevska Williams and Yinzhan Xu, "Hardness for Triangle Problems under Even More Believable Hypotheses: Reductions from Real APSP, Real 3SUM, and OV", STOC (2022), arXiv:2203.08356.
