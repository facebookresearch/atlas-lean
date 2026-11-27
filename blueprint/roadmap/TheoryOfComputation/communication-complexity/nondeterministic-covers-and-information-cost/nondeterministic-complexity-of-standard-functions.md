# Nondeterministic complexity of equality, disjointness and inner product

For $n$-bit strings with $n \ge 1$: $N^1(\mathrm{EQ}_n) = n$ and $N^0(\mathrm{EQ}_n) \le \lceil\log_2 n\rceil + 1$; $N^1(\mathrm{DISJ}_n) = n$ and $N^0(\mathrm{DISJ}_n) \le \lceil \log_2 n \rceil$ (equivalently $N^0$ of intersection is $n$); for the inner product modulo two, $N^1(\mathrm{IP}_n) \ge n - 1$ and $N^0(\mathrm{IP}_n) \ge n$. So nondeterminism helps exponentially for one answer of equality and disjointness but not for inner product.

## Proof sketch

Lower bounds come from fooling sets of size $2^n$ (diagonal pairs for equality, complementary pairs for disjointness), since a $z$-rectangle of a cover, like a rectangle of a partition, contains at most one element of a fooling set with value $z$, and, for inner product, from the fact that a monochromatic rectangle of $\mathrm{IP}_n$ of either colour has at most $2^n$ entries (Lindsey's lemma: $|\mathbf 1_A^{\mathsf T} H \mathbf 1_B| \le 2^{n/2}\sqrt{|A||B|}$ for the Hadamard sign matrix $H$, whose spectral norm is $2^{n/2}$), while $\mathrm{IP}_n$ has $2^{2n-1}-2^{n-1}$ ones and $2^{2n-1}+2^{n-1}$ zeros. Upper bounds guess a position where the inputs differ, or a common element.

## Depends on

- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)
- [Equality function](../deterministic-communication-protocols/eq-fn.md)
- [Set intersection function](../randomized-communication-protocols/disj-fn.md)

## Proof depends on

- [Fooling sets bound the tiling number](../rectangle-partitions-and-deterministic-bounds/fooling-sets-bound-the-tiling-number.md)
- [Uniform discrepancy is bounded by the spectral norm of the sign matrix](../discrepancy-corruption-and-sign-rank/spectral-bound-on-uniform-discrepancy.md)
- [The inner-product matrix has full rank](../rectangle-partitions-and-deterministic-bounds/inner-product-matrix-has-full-rank.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
