# The rank of the communication matrix bounds the tiling number

Let $K$ be a field and $M_f$ the $0/1$ communication matrix over $K$ of a Boolean $f : X \times Y \to \{0,1\}$ on finite sets. For every labelled rectangle partition for $f$, $\mathrm{rank}_K(M_f)$ is at most the number of rectangles labelled $1$; hence $\mathrm{rank}_K(M_f) \le \chi(f)$. Over a semiring \"rank\" is ambiguous: over the Boolean semiring the six rows of the $6 \times 4$ matrix of two-element subsets of a four-element set need six generators, although four column rectangles partition its ones, so the field rank should not be replaced by a semiring rank without saying which one (for instance the least inner dimension of a factorization, which the rectangles bound).

## Proof sketch

$M_f$ is the sum, over the $1$-labelled rectangles $A \times B$, of the rank-one matrices $\mathbf{1}_A \mathbf{1}_B^{\mathsf T}$, and rank is subadditive.

## Depends on

- [Monochromatic rectangle partitions and the tiling number](monochromatic-rectangle-partitions-and-tiling-number.md)
- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
