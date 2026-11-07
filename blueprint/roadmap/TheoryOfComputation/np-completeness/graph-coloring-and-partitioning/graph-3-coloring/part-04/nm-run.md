# Moving the current name from $T$ to $A$

Let $m$ be a quiescent state of the 3-COLOR
emitter whose stack $A$ is empty, $v$ a bit, $x \in \mathbb{N}$, and $R$ a list of token symbols
whose first element, if any, is not a name bit. If the token stack $T$ of $m$ is the name of $x$
in reverse order followed by $R$, then for some bit $v'$ the emitter machine runs in exactly
$k + 1$ steps, where $k$ is the length of the binary encoding of $x$, from label $\mathtt{nm}$
with internal bit $v$ and the stacks of $m$ to label $\mathtt{walk}$ with internal bit $v'$ and
the stacks of the quiescent state obtained from $m$ by setting $T$ to $R$ and $A$ to the name
of $x$.
