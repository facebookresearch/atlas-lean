# Chandra–Furst–Lipton: Exactly-N has unbounded NOF complexity

In the three-player *Exactly-N* problem, player $i \in \{0,1,2\}$ has $x_i \in \{0, \dots, N\}$ on their forehead and the players must decide whether $x_0 + x_1 + x_2 = N$. Its deterministic NOF communication complexity tends to infinity as $N \to \infty$. More precisely, a protocol of cost $c$ partitions the yes-instances into at most $2^c$ classes each of which is corner-free, so $2^c$ is at least the minimum number of colours in a corner-free colouring of the grid $\{(a,b) : a + b \le N\}$.

## Proof sketch

Map each yes-input $(a, b, N - a - b)$ to the point $(a, b)$. If three yes-inputs forming a corner $(x, y), (x, y + \lambda), (x + \lambda, y)$ reach the same leaf, then the "apex" $(x, y, N - x - y - \lambda)$, which each player cannot distinguish from one of the three, reaches the same accepting leaf although it is a no-instance. So each leaf class is corner-free (corners with $\lambda \ge 1$). The number of colours needed tends to infinity by the density Hales–Jewett theorem for $k = 3$: map $u \in \{0,1,2\}^N$ to the grid point $(\#\{j : u_j = 0\}, \#\{j : u_j = 1\})$. A combinatorial line with $\lambda \ge 1$ free coordinates and fixed part having $a$ zeros and $b$ ones maps to the corner $(a, b), (a + \lambda, b), (a, b + \lambda)$, so a corner-free colouring of the grid with $c$ colours would give a colouring of $\{0,1,2\}^N$ whose largest class, of density at least $1/c$, contains no line, which fails for $N$ large.

## Depends on

- [Number-on-forehead protocols and cylinder intersections](number-on-forehead-protocols.md)

## Proof depends on

- [Density Hales–Jewett theorem](../../../Combinatorics/ramsey-theory/structural-ramsey/density-hales-jewett-theorem/density-hales-jewett.md)

## Sources

- A. K. Chandra, M. L. Furst and R. J. Lipton, "Multi-Party Protocols", STOC 1983.
- A. Rao and A. Yehudayoff, "Communication Complexity and Applications", Cambridge University Press, 2020.
