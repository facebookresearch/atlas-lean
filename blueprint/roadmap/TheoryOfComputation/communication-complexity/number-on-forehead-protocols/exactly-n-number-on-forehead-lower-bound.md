# Chandra–Furst–Lipton: Exactly-N has unbounded NOF complexity

In the three-player *Exactly-N* problem, player $i \in \{0,1,2\}$ has $x_i \in \{0, \dots, N\}$ on their forehead and the players must decide whether $x_0 + x_1 + x_2 = N$. Its deterministic NOF communication complexity tends to infinity as $N \to \infty$. More precisely, a protocol of cost $c$ partitions the yes-instances into at most $2^c$ classes each of which is corner-free, so $2^c$ is at least the minimum number of colours in a corner-free colouring of the grid $\{(a,b) : a + b \le N\}$.

## Proof sketch

Map each yes-input $(a, b, N - a - b)$ to the point $(a, b)$. If three yes-inputs forming a corner $(x, y), (x, y + \lambda), (x + \lambda, y)$ reach the same leaf, then the "apex" $(x, y, N - x - y - \lambda)$, which each player cannot distinguish from one of the three, reaches the same accepting leaf although it is a no-instance. So each leaf class is corner-free, and the corners theorem (a density version of Szemerédi-type results in two dimensions) shows corner-free subsets have density $o(1)$.

## Depends on

- [Number-on-forehead protocols and cylinder intersections](number-on-forehead-protocols.md)

## Proof depends on

- [Szemerédi's theorem](../../../Combinatorics/additive-combinatorics/progressions-dense-sets/szemeredi.md)

## Sources

- A. K. Chandra, M. L. Furst and R. J. Lipton, "Multi-Party Protocols", STOC 1983.
- A. Rao and A. Yehudayoff, "Communication Complexity and Applications", Cambridge University Press, 2020.
