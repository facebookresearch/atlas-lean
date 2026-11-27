# Rectangle lemma

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The transcript of the run on $(x, y)$ is the list of bits announced. For every protocol $p$, every list of bits $\pi$, $x \in X$ and $y \in Y$: the run of $p$ on $(x, y)$
has transcript $\pi$ if and only if there is $y' \in Y$ such that the run on $(x, y')$ has transcript $\pi$ and
there is $x' \in X$ such that the run on $(x', y)$ has transcript $\pi$. Hence the inputs with transcript
$\pi$ form a combinatorial rectangle $A \times B$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Lemmas 1.5 and 1.6.
