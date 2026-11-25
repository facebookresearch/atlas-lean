# Alice reveals her input from a list

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. For a list $a_1, \dots, a_k$ of elements of $X$ and protocols $p_a$ indexed by $a \in X$, the protocol in
which Alice reveals her input from the list is defined recursively: for the empty list it is the leaf with
output $0$; for the list $a_1, a_2, \dots, a_k$ it is the Alice node announcing whether $x = a_1$ (bit $1$
if so), whose $1$-child is $p_{a_1}$ and whose $0$-child is the protocol for the list $a_2, \dots, a_k$.
Thus inputs not in the list end at a leaf with output $0$.
