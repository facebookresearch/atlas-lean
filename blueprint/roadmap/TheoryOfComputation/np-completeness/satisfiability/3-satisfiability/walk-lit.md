# Walking over a literal advances the literal count

Let $\mathrm{cap}$ be a Boolean and
$n \in \mathbb{N}$ with $\mathrm{cap}$ false or $n < 3$; stacks are lists written top first,
$w_m$ is the walking label after $m$ literals, $\mathrm{bit}(b)$ is the name-bit symbol carrying
the Boolean $b$ and $\mathrm{lit}(p)$ is the polarity marker of polarity $p$. Let $l = (i, p)$ be
a literal with variable index $i \in \mathbb{N}$ and polarity $p$, let $e_1, \dots, e_k$ be the
binary encoding $\mathrm{encodeNat}(i)$ of $i$, let $R$ and $U$ be lists of symbols and $v$ a
Boolean. Then there is a Boolean $v'$ such that the clause-length filter with cap flag
$\mathrm{cap}$ goes in exactly $k + 1$ steps from label $w_n$, local variable $v$, token stack
$\mathrm{lit}(p), \mathrm{bit}(e_k), \dots, \mathrm{bit}(e_1)$ on top of $R$ and side stack $U$
to label $w_{n+1}$, local variable $v'$, token stack $R$ and side stack
$\mathrm{bit}(e_1), \dots, \mathrm{bit}(e_k), \mathrm{lit}(p)$ on top of $U$.
