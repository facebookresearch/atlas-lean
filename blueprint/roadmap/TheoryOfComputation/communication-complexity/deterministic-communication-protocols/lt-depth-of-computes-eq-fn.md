# Lower bound for equality

For $n \in \mathbb{N}$, the equality function $\mathrm{EQ}_n : \{0,1\}^n \times \{0,1\}^n \to \{0, 1\}$ is $1$ exactly on pairs $(x, y)$ with $x = y$. Here protocols have inputs $X = Y = \{0,1\}^n$. A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. Let $n \ge 1$. Every protocol computing $\mathrm{EQ}_n$ has depth at least $n + 1$.

The $2^n$ diagonal pairs reach distinct leaves with output $1$, and some further leaf has output $0$.

## Informally uses

- [Leaf rectangles are monochromatic](eq-of-transcript-eq.md): two diagonal pairs in one leaf rectangle would force $\mathrm{EQ}(x, x') = 1$ (Rao and Yehudayoff, Claim 1.13).
- [A protocol of depth $d$ has at most $2^d$ leaves](card-leaves-le.md): $2^n$ leaves with output $1$ and one with output $0$ need depth at least $n + 1$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Claim 1.13 and Theorem 1.14.
