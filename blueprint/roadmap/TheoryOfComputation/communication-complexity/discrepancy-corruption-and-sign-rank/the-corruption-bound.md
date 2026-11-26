# The corruption (rectangle) bound

Let $\nu$ be a distribution on $X \times Y$ and $z$ an output value. Say $f$ is $(\alpha, \delta)$-corrupted on $z$ under $\nu$ if every rectangle $R$ satisfies $\nu(R \setminus f^{-1}(z)) \ge \alpha\, \nu(R \cap f^{-1}(z)) - \delta$. Then every deterministic protocol of cost $c$ with distributional error $\varepsilon$ under $\nu$ satisfies

$$\alpha\big(\nu(f^{-1}(z)) - \varepsilon\big) \le \varepsilon + 2^c \delta,$$

and by Yao's principle the same bound holds for public-coin protocols with worst-case error $\varepsilon$.

## Proof sketch

Sum the corruption inequality over the leaf rectangles labelled $z$: their total $f^{-1}(z)$-mass is at least $\nu(f^{-1}(z)) - \varepsilon$, while their non-$z$ mass is part of the error, and there are at most $2^c$ leaves.

## Depends on

- [Distributional communication complexity](../randomized-communication-protocols/dist-complexity.md)
- [Monochromatic rectangle partitions and the tiling number](../rectangle-partitions-and-deterministic-bounds/monochromatic-rectangle-partitions-and-tiling-number.md)

## Proof depends on

- [Yao's minimax principle for communication complexity](../randomized-communication-protocols/rand-complexity-eq-i-sup-dist-complexity.md)

## Sources

- A. A. Razborov, "On the Distributional Complexity of Disjointness", Theoretical Computer Science 106(2), 1992.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
