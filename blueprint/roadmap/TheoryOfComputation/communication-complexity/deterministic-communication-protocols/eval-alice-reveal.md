# Alice reveals her input

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. Let $a_1, \dots, a_k$ be a list of elements of $X$, let $p_a$ be protocols indexed by $a \in X$, and let
$R$ be the protocol in which Alice reveals her input from the list (an Alice node asking whether $x = a_1$,
leading to $p_{a_1}$ if so and otherwise to the protocol for $a_2, \dots, a_k$; the empty list giving the
leaf with output $0$). If $x$ occurs in the list, then for every $y \in Y$ the output of $R$ on $(x, y)$
equals the output of $p_x$ on $(x, y)$.
