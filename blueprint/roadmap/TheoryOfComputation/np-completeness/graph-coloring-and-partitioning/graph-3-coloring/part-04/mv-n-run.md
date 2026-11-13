# Moving an earlier name from $D$ to $E$

Let $m$ be a quiescent state of the 3-COLOR
emitter, $v$ a bit, $r$ either empty or a bit $b$, $w$ a list of bits, and $R$ a list of token
symbols whose first element, if any, is not a name bit. If the stack $D$ of $m$ is the name bits
of $w$ followed by $R$, then for some bit $v'$ the emitter machine runs in exactly $|w| + 1$
steps from label $\mathtt{mvN}(r)$ with internal bit $v$ and the stacks of $m$ to internal bit
$v'$, label $\mathtt{skU}$ if $r$ is empty and $\mathtt{mvU}(b)$ if $r = b$, and the stacks of
the quiescent state obtained from $m$ by setting $D$ to $R$ and putting the name bits of $w$, in
reverse order, on top of $E$.
