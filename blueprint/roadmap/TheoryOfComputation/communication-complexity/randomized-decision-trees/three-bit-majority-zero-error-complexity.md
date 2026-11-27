# Three-bit majority has zero-error expected query complexity exactly 8/3

For majority on three bits, $R_0(\mathrm{MAJ}_3) = 8/3$. The algorithm that queries the bits in a uniformly random order and stops as soon as the value is determined has expected cost $2$ on the constant inputs and $8/3$ on the six nonconstant inputs; conversely, under the uniform distribution on the six nonconstant inputs, every deterministic tree computing majority, even one allowed repeated queries, has expected cost at least $8/3$.

## Proof sketch

On a nonconstant input two of the bits agree; a random order stops after two queries exactly when the first two queried bits agree, with probability $1/3$, giving $2 \cdot \frac13 + 3 \cdot \frac23 = 8/3$. For the lower bound, any tree must query a third bit whenever the first two disagree, which under the hard distribution happens with probability $2/3$; Yao's principle concludes.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)
- [Majority function](../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/majority.md)

## Proof depends on

- [Yao's minimax principle for bounded-error and zero-error decision trees](yao-minimax-for-decision-trees.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
