# Graph connectivity is evasive

For every $m$, the function deciding whether a labelled simple graph on vertex set $[m]$ (given by its $\binom{m}{2}$ edge indicator bits) is connected has deterministic decision tree complexity exactly $\binom{m}{2}$ (with the conventions that the graph on one vertex is connected and the empty graph is not; both then have complexity $0$).

## Proof sketch

Adversary argument: answer "no edge" to a queried pair unless that answer would disconnect the graph formed by the unqueried and present edges, i.e. unless the queried edge is a bridge of the graph of all non-excluded pairs. The adversary maintains that the answer remains undetermined until the last pair is queried.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- R. L. Rivest and J. Vuillemin, "On Recognizing Graph Properties from Adjacency Matrices", Theoretical Computer Science 3(3), 1976.
