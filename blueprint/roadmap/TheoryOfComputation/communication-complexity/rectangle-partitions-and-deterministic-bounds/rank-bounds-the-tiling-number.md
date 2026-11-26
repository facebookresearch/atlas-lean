# The rank of the communication matrix bounds the tiling number

Let $M_f$ be the $0/1$ communication matrix of a Boolean $f : X \times Y \to \{0,1\}$ over a commutative semiring with the strong rank condition (for example any field). For every labelled rectangle partition for $f$, $\mathrm{rank}(M_f)$ is at most the number of rectangles labelled $1$; hence $\mathrm{rank}(M_f) \le \chi(f)$.

## Proof sketch

$M_f$ is the sum, over the $1$-labelled rectangles $A \times B$, of the rank-one matrices $\mathbf{1}_A \mathbf{1}_B^{\mathsf T}$, and rank is subadditive.

## Depends on

- [Monochromatic rectangle partitions and the tiling number](monochromatic-rectangle-partitions-and-tiling-number.md)
- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
