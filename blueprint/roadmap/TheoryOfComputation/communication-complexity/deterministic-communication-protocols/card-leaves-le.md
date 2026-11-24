# A protocol of depth $d$ has at most $2^d$ leaves

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). The set of leaves of a protocol $p$, each leaf identified with the list of bits along its
root-to-leaf path, has at most $2^d$ elements, where $d$ is the depth of $p$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Lemma 1.2.
