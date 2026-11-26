# Emitting one literal occurrence

Let $\ell = (x, p)$ be a literal, $R$ a list of token
symbols whose first element, if any, is not a name bit, and $qs$ a list of earlier occurrences
$(x_i, p_i, L_i, M_i)$ with $M_i = L_i + 1$ for each. Let $m$ be a quiescent state of the
3-COLOR emitter with counter values $n$ for $N$ and $r$ for the OR output, and $v$ a bit.
Suppose the token stack of $m$ is the tokens of $\ell$ (its polarity marker above its name in
reverse order) followed by $R$, the stack $D$ is the concatenated stack encodings of the
occurrences in $qs$, the stacks $E$, $A$, $P$ are empty and the counter $U$ is $0$. Let $d$ be
the length of $D$ and $k$ the length of the binary encoding of $x$. Then for some bit $v'$ the
emitter machine runs in at most
$13 d + |qs| (8 (n + r) + 21) + 10 (n + r) + 3 k + 30$
steps from label $\mathtt{lits}$ with internal bit $v$ and the stacks of $m$ to label
$\mathtt{aft}$ with internal bit $v'$ and the stacks of the quiescent state obtained from $m$
as follows: the token stack is $R$; $D$ holds the stack encodings of $(x, p, n, n + 1)$ and then
of the occurrences in $qs$; and the output is the old output with the edges $(n, n + 1)$,
$(n, 2)$, $(n + 1, 2)$ and then the consistency edges of the new occurrence $(\ell, n, n + 1)$
with the occurrences in $qs$, in order, pushed on top. The counter $N$ is not advanced.
