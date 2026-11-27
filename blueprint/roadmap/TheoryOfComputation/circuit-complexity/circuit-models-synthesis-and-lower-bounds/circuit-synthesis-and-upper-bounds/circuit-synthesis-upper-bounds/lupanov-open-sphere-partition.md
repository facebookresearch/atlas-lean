# Lupanov's partition of a power-of-two cube into open spheres

For every $r\ge 0$ and $d=2^r$ there is a set $C\subseteq\{0,1\}^d$ with $|C|\cdot d=2^d$ such that the map $(c,i)\mapsto c\oplus e_i$ is a bijection from $C\times\{1,\dots,d\}$ onto $\{0,1\}^d$. Equivalently, the radius-one Hamming spheres around the points of $C$, with their centers removed, are pairwise disjoint and cover the whole cube.

## Proof sketch

Let $H\subseteq\{0,1\}^{d-1}$ be the Hamming code of length $d-1=2^r-1$, which is perfect with covering radius one, and take $C=H\times\{0,1\}$, so $|C|=2^d/d$. A point $(x,b)$ with $x\notin H$ is the neighbour $(h\oplus e_i,b)$ of exactly one center, and a point $(h,b)$ with $h\in H$ is the neighbour of exactly the center $(h,1-b)$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- O. B. Lupanov, "On the Realization of Functions of Logical Algebra by Formulae of Finite Classes (Formulae of Limited Depth) in the Basis ∧, ∨, ¬", Problemy Kibernetiki, 1961.
- F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes", North-Holland, 1977 (perfect Hamming codes).
