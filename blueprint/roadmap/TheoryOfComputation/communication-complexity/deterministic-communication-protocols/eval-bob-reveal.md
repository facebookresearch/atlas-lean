# Bob reveals his input

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. Let $b_1, \dots, b_k$ be a list of elements of $Y$, let $p_b$ be protocols indexed by $b \in Y$, and let
$R$ be the protocol in which Bob reveals his input from the list (a Bob node asking whether $y = b_1$,
leading to $p_{b_1}$ if so and otherwise to the protocol for $b_2, \dots, b_k$; the empty list giving the
leaf with output $0$). If $y$ occurs in the list, then for every $x \in X$ the output of $R$ on $(x, y)$
equals the output of $p_y$ on $(x, y)$.
