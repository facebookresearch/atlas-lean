# Deciding majority requires linearly many randomized probes

For $n \ge 1$, every finitely supported mixture of adaptive decision trees computing majority on $n$ bits (at least $\lceil n/2 \rceil$ ones) with error at most $1/3$ on every input has an input $x$ and a supported tree $t$ with

$$\Big\lfloor \frac{n}{2} \Big\rfloor + 1 \le 3 \cdot \mathrm{cost}(t, x),$$

where cost counts executed probes including repeats. So $R_{1/3}(\mathrm{MAJ}_n) = \Omega(n)$, in contrast with property testing of majority, which needs only $O(1/\varepsilon^2)$ samples.

## Proof sketch

$bs(\mathrm{MAJ}_n) = s(\mathrm{MAJ}_n) = \lfloor n/2 \rfloor + 1$ (flip any single coordinate at a weight-threshold input), and Nisan's bound gives expected cost at least $(1 - 2/3)\, bs$ on some input; a supported tree attains at least the expectation.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)
- [Majority function](../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/majority.md)

## Proof depends on

- [Nisan: block sensitivity and approximate degree lower-bound randomized query complexity](nisan-randomized-query-lower-bounds.md)
- [Query measures of threshold functions](../sensitivity-certificates-and-degree/query-measures-of-threshold-functions.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
