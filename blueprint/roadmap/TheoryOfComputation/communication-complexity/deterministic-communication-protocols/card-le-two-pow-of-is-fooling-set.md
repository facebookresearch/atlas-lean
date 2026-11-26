# Fooling-set lower bound

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. A finite set $S \subseteq X \times Y$ is a fooling set for $f$ with value $b \in \{0, 1\}$ if $f(x, y) = b$ for all $(x, y) \in S$ and, for any two distinct pairs $(x_1, y_1), (x_2, y_2) \in S$, $f(x_1, y_2) \ne b$ or $f(x_2, y_1) \ne b$. If a protocol $p$ computes $f : X \times Y \to \{0, 1\}$ and $S$ is a fooling set for $f$
with some value $b$, then $|S| \le 2^{d}$, where $d$ is the depth of $p$.

## Informally uses

- [Crossing property of transcripts](transcript-cross.md): two fooling pairs with the same transcript would give the crossed pairs that transcript too, as in Arora and Barak's proof of Lemma 12.4.
- [A protocol of depth $d$ has at most $2^d$ leaves](card-leaves-le.md): the pigeonhole step counts at most $2^d$ transcripts.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Lemma 12.4.
