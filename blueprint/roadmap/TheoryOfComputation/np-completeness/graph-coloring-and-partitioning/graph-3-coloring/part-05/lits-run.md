# The emitter processes the remaining literals of a clause

Let $L_b \in \mathbb{N}$, let
$R$ be a list of token symbols that is empty or starts with the clause token $\mathtt{cl}$, and
let $o_0$ be a list of bits. Let $ls$ be a list of literals, $o, \tau \in \mathbb{N}$, $s$ a
construction state and $v$ a bit, and write $T$ for the concatenation of the token-stack tokens
of the literals of $ls$ and $TR$ for $T$ followed by $R$. Suppose $s$ satisfies the size
invariant after $\tau$ tokens, $o$ is at most the next free vertex of $s$, and
$\tau + |T| \le L_b$. Then for some bit $v'$ the emitter machine runs in at most
$(|T| + 1) \cdot \mathrm{budget}(L_b)$ steps from label $\mathtt{lits}$ with internal bit $v$
and the stacks of the quiescent state $\mathrm{enc}(s, TR, o_0, o, 0)$ to label $\mathtt{cls}$
with internal bit $v'$ and the stacks of $\mathrm{enc}(\mathrm{colLits}(ls, o, s), R, o_0, 0, 0)$.
Here $\mathrm{enc}(s, t, o_0, r, f)$ is the quiescent state of $s$ with token stack $t$, output
above $o_0$, OR output $r$ and first-literal flag $f$; $\mathrm{colLits}(ls, o, s)$ is $s$ after
the occurrences and OR gadgets of $ls$, starting from OR output $o$, and the clause end; and
$\mathrm{budget}(L_b) = 400 (L_b + 1)^2$.
