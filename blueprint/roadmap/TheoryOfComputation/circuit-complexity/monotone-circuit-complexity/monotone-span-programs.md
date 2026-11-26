# Monotone span programs

A *monotone span program* over a field $F$ for a set of parties $\{1,\dots,N\}$ assigns to each party $i$ a matrix $M_i$ over $F$ with $d$ columns ($d\ge1$). A coalition $S\subseteq\{1,\dots,N\}$ is *accepted* if the target vector $e_1=(1,0,\dots,0)\in F^d$ lies in the span of the rows of the matrices $M_i$, $i\in S$. The accepted coalitions form a monotone family. The *size* of the program is the total number of rows.

## Depends on

- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Sources

- Dan Boneh, Victor Shoup, "A Graduate Course in Applied Cryptography", 2023.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
