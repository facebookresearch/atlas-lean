# Monochromatic rectangle partitions and the tiling number

Let $f : X \times Y \to Z$ with $X, Y$ finite. A *labelled rectangle partition* of $X \times Y$ is a finite family of combinatorial rectangles $R_i = A_i \times B_i$ ($A_i \subseteq X$, $B_i \subseteq Y$), pairwise disjoint with union $X \times Y$, each carrying a label $z_i \in Z$; it is *for* $f$ if $f(x,y) = z_i$ on $R_i$. The *tiling number* $\chi(f)$ is the least number of rectangles in a partition for $f$. By the rectangle lemma the leaves of a protocol tree of depth $c$ computing $f$ form such a partition, so $\chi(f) \le 2^{D(f)}$ for Boolean $f$, where $D(f)$ is the deterministic communication complexity (protocols with leaves labelled in $Z$ give the same bound for general $f$). For Boolean $f$, $\chi(f)$ is the partition number of [Partition number and unambiguous certificate complexity](../randomized-and-dag-like-lifting/partition-number.md).

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Rectangle lemma](../deterministic-communication-protocols/transcript-eq-iff.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
