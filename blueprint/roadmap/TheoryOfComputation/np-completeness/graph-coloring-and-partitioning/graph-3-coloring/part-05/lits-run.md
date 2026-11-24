# The emitter processes the remaining literals of a clause

Let $L_b \in \mathbb{N}$, let $R$ be a list of token symbols that is empty or starts with the
clause token $\mathtt{cl}$, and let $o_0$ be a list of bits. Let $ls$ be a list of literals,
$o, \tau \in \mathbb{N}$, $s$ a construction state and $v$ a bit, and write $T$ for the
concatenation of the token-stack tokens of the literals of $ls$ and $TR$ for $T$ followed by $R$.
Suppose $s$ satisfies the [size invariant](inv.md) after $\tau$ tokens, $o$ is at most the next
free vertex of $s$, and $\tau + |T| \le L_b$. Let $s'$ be the state obtained from $s$ by
[processing the remaining literals](../part-01/col-lits.md) $ls$ with output so far $o$ (their
occurrences and OR gadgets, then the clause end). Then for some bit $v'$ the emitter machine runs
in at most $(|T| + 1) \cdot 400 (L_b + 1)^2$ steps from label $\mathtt{lits}$ with internal bit
$v$ and the stacks of the [emitter state](enc.md) of $s$ with token stack $TR$, output above
$o_0$, OR output $o$ and first-literal flag $0$, to label $\mathtt{cls}$ with internal bit $v'$
and the stacks of the emitter state of $s'$ with token stack $R$, output above $o_0$, OR output
$0$ and first-literal flag $0$.
