# Randomized decision trees and their complexities

A *randomized decision tree* is a probability distribution with finite support over deterministic decision trees. It computes $f$ with error $\varepsilon$ if for every input $x$ the probability that the drawn tree outputs $f(x)$ is at least $1 - \varepsilon$. Its worst-case cost is the maximum depth of a tree in its support, and its *expected cost* on $x$ is the expected number of queries executed on $x$ (repeated queries counted).

- For $0 < \varepsilon < 1/2$, the *bounded-error complexity* $R_\varepsilon(f)$ is the least worst-case cost of a randomized tree computing $f$ with error $\varepsilon$. The same definition at $\varepsilon = 0$ forces every supported tree to compute $f$ exactly and gives $D(f)$, so it gets no separate symbol.
- The *zero-error (Las Vegas) complexity* $R_0(f)$ is the least, over randomized trees whose every supported tree computes $f$ exactly, of the maximum over inputs of the expected cost. It can be smaller than $D(f)$: three-bit majority has $D = 3$ and $R_0 = 8/3$.
- For a distribution $\mu$ on inputs, the *distributional complexity* $D^\mu_\varepsilon(f)$ is the least depth of a deterministic tree whose probability of error under $\mu$ is at most $\varepsilon$.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
