# Additive circuits and the active square of a Boolean matrix

Let $(G,+,0)$ be a commutative monoid. An *additive circuit* over $\{0,+\}$ computes, for a Boolean $m\times n$ matrix $A$, the map $G^n\to G^m$, $x\mapsto(\sum_{j:A_{ij}=1}x_j)_i$; its size is the number of addition gates. The *active square* $S(A)$ of $A$ is the number of positions $(i,j)$ lying within horizontal distance $\lfloor\log_2 m\rfloor$ of a one-entry in the same row.

## Depends on

- [Rectifier (OR) circuits for Boolean matrices](rectifier-or-circuits.md)

## Sources

- Igor S. Sergeev, "A relation between additive and multiplicative complexity of Boolean functions", 2013.
