# Nonconstant symmetric functions are evasive

Every nonconstant symmetric function $f : \{0,1\}^n \to \{0,1\}$ (one depending only on the Hamming weight) has decision tree complexity $n$. In particular threshold functions $\mathrm{Th}^n_j$ with $1 \le j \le n$, majority and parity are evasive, although the sensitivity of majority is only about $n/2$.

## Proof sketch

Choose a weight $k$ where the weight profile changes value. The adversary answers queries so that the number of ones among the queried bits stays compatible with total weight both $k$ and $k+1$ until all bits are read; formally, on subcubes whose output depends only on the number of true free bits through a profile with a change point, every tree must query all free coordinates.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
