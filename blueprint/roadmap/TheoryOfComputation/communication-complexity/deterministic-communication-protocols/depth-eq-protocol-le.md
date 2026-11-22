# Upper bound for equality

For $n \in \mathbb{N}$, the equality function $\mathrm{EQ}_n : \{0,1\}^n \times \{0,1\}^n \to \{0, 1\}$ is $1$ exactly on pairs $(x, y)$ with $x = y$. Here protocols have inputs $X = Y = \{0,1\}^n$. A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). The trivial protocol for $\mathrm{EQ}_n$: Alice sends her $n$ bits, after which Bob announces one bit, $1$ if the message equals his input and $0$ otherwise, and the leaves output the bit Bob announced. For every $n \in \mathbb{N}$, the trivial protocol for $\mathrm{EQ}_n$ has depth at most $n + 1$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 1: "Alice can send Bob her input, and Bob can respond with the value of a function, giving a protocol with communication $n + 1$".
