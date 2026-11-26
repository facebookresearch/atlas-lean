# Discrepancy bounds the tiling number

For every Boolean $f$ on finite nonempty sets and every probability distribution $\nu$ on $X \times Y$,

$$1 \le \chi(f) \cdot \mathrm{disc}_\nu(f), \qquad\text{that is}\qquad \frac{1}{\mathrm{disc}_\nu(f)} \le \chi(f).$$

## Proof sketch

In a partition for $f$ each rectangle is monochromatic, so $\sum_{R}\big|\sum_{R} \nu (-1)^f\big| = \sum_{X\times Y}\nu = 1$, while each summand is at most $\mathrm{disc}_\nu(f)$.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)
- [Monochromatic rectangle partitions and the tiling number](../rectangle-partitions-and-deterministic-bounds/monochromatic-rectangle-partitions-and-tiling-number.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
