# Moving an earlier literal vertex from $D$ to $U$

Let $m$ be a quiescent state of the
3-COLOR emitter whose counter $U$ is $0$, let $v$ and $b$ be bits, $j \in \mathbb{N}$, and $R$ a
list of token symbols whose first element, if any, is not the clause token $\mathtt{cl}$. If
the stack $D$ of $m$ is $j$ copies of $\mathtt{cl}$ followed by $R$, then for some bit $v'$ the
emitter machine runs in exactly $j + 1$ steps from label $\mathtt{mvU}(b)$ with internal bit $v$
and the stacks of $m$ to label $\mathtt{pre}(c_1)$ if $b$ is true and $\mathtt{pre}(d_1)$ if $b$
is false, internal bit $v'$, and the stacks of the quiescent state obtained from $m$ by setting
$D$ to $R$ and $U$ to $j$.
