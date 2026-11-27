# Unambiguous covers, partition number and SUM-rank

An *unambiguous* (partition) $z$-cover of a partial Boolean matrix is a $z$-cover in which every entry where the answer must be $z$ lies in exactly one rectangle (rectangles may overlap on don't-care entries). The *partition cover number* $\mathrm{UC}^z(f)$ is its least size. Always $C^z(f) \le \mathrm{UC}^z(f) \le \chi(f)$.

$\mathrm{UC}^1(f)$ equals the least number of $0/1$ rank-one matrices (indicators of rectangles) whose sum agrees with $f$ on its defined entries, where on don't-care entries the sum may take **any natural value**, not only $0$ or $1$. For a total Boolean matrix this is the least rank of a factorization $M_f = \sum_k u_k v_k^{\mathsf T}$ over the semiring $(\mathbb{N}, +, \cdot)$ (the SUM-rank), since every term of such a factorization of a $0/1$ matrix is the indicator of a rectangle. For partial matrices the natural-valued convention is needed: in $\begin{pmatrix} 1 & 1 & 0 \\ 1 & * & 1 \\ 0 & 1 & 1 \end{pmatrix}$ the two diagonal $2 \times 2$ squares form an unambiguous $1$-cover whose sum is $2$ at $*$, while filling $*$ with a Boolean value $t$ gives determinant $t - 2 \ne 0$, so no Boolean completion is a sum of two rank-one matrices. Requiring the rectangles to be disjoint on every entry instead gives the least number of rectangle indicators summing to a Boolean completion.

## Depends on

- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)
- [Monochromatic rectangle partitions and the tiling number](../rectangle-partitions-and-deterministic-bounds/monochromatic-rectangle-partitions-and-tiling-number.md)
- [Nonnegative rank of a matrix](../../../ComputerScience/machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Deterministic Communication vs. Partition Number", SIAM Journal on Computing 47(6), 2018.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
