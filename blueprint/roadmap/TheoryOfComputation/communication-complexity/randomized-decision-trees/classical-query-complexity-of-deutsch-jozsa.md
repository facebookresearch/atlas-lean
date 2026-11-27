# Classical query complexity of the Deutsch–Jozsa problem

In the Deutsch–Jozsa promise problem on $N = 2m$ bits with $m \ge 1$ (the input is constant or balanced, and only promised inputs count), every deterministic algorithm needs $m + 1$ queries in the worst case, and $m + 1$ queries suffice. With randomness and error $\varepsilon \in (0, 1/2]$, $1 + \lceil \log_2(1/\varepsilon) \rceil$ queries suffice: query $k$ independent uniformly random positions and answer "constant" iff all answers agree; this is always correct on constant inputs and errs on balanced inputs with probability at most $2^{1-k}$. Hence the quantum advantage for this problem holds only against exact algorithms.

## Proof sketch

Deterministic lower bound: an adversary answers the first $m$ queries with equal bits; both a constant input and a balanced input remain consistent. Randomized upper bound: on a balanced input the $k$ independent samples agree with probability $2 \cdot 2^{-k}$.

## Depends on

- [Randomized decision trees and their complexities](randomized-decision-trees.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- D. Deutsch and R. Jozsa, "Rapid Solution of Problems by Quantum Computation", Proceedings of the Royal Society of London A 439, 1992.
- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
