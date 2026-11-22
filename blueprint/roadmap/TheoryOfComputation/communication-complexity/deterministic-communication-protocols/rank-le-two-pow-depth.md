# Rank lower bound

Let $X$ be a set and $Y$ a finite set (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. For a field $K$, the communication matrix $M_f$ of $f$ over $K$ is the $X \times Y$ matrix with entry $1$ at $(x, y)$ if $f(x, y) = 1$ and $0$ otherwise. For every field $K$, if a
protocol $p$ computes $f : X \times Y \to \{0, 1\}$, then $\operatorname{rank}_K M_f \le 2^{d}$, where $d$ is the
depth of $p$; equivalently $d \ge \log_2 \operatorname{rank}_K M_f$.

## Informally uses

- [Leaf rectangles are monochromatic](eq-of-transcript-eq.md): Rao and Yehudayoff derive the bound from the partition of the inputs into monochromatic leaf rectangles (their Theorem 1.7).
- [A protocol of depth $d$ has at most $2^d$ leaves](card-leaves-le.md): the number of rectangles, hence of rank-one summands, is at most $2^d$.

## Background

- [Rank of a product of matrices](../../../LinearAlgebra/linear-maps-and-duality/rank-of-a-product.md): writing $M_f = UV$ with $U$ and $V$ indexed by the leaves shows that the rank is at most the number of leaves; the source sums rank-one matrices instead.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Lemma 2.10 and Theorem 2.11.
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Theorem 12.10 ($\chi(f) \ge \operatorname{rank} M(f)$) with Theorem 12.7 ($C(f) \ge \log_2 \chi(f)$).
