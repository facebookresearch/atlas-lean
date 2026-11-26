# Unambiguous covers, partition number and SUM-rank

An *unambiguous* (partition) $z$-cover of a partial Boolean matrix is a $z$-cover in which every entry where the answer must be $z$ lies in exactly one rectangle (rectangles may overlap on don't-care entries). The *partition cover number* $\mathrm{UC}^z(f)$ is its least size. Always $C^z(f) \le \mathrm{UC}^z(f) \le \chi(f)$. On all of $X \times Y$, $\mathrm{UC}^1(f)$ equals the least rank over the semiring $(\mathbb{N}, +, \cdot)$ (the SUM-rank, or Boolean-to-natural nonnegative rank) among completions of the partial $0/1$ matrix, i.e. the least number of $0/1$ rank-one matrices summing to a completion.

## Depends on

- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)
- [Monochromatic rectangle partitions and the tiling number](../rectangle-partitions-and-deterministic-bounds/monochromatic-rectangle-partitions-and-tiling-number.md)
- [Nonnegative rank of a matrix](../../../ComputerScience/machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Deterministic Communication vs. Partition Number", SIAM Journal on Computing 47(6), 2018.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
