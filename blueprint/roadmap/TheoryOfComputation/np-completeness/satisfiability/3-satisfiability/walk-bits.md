# Walking over name bits keeps the label

Let $\mathrm{cap}$ be a Boolean, $n \in \mathbb{N}$
and $R$ a list of symbols; stacks are lists written top first, $w_n$ is the walking label after
$n$ literals and $\mathrm{bit}(b)$ is the name-bit symbol carrying the Boolean $b$. For all
Booleans $b_1, \dots, b_k$, every list of symbols $U$ and every Boolean $v$ there is a Boolean
$v'$ such that the clause-length filter with cap flag $\mathrm{cap}$ goes in exactly $k$ steps
from label $w_n$, local variable $v$, token stack $\mathrm{bit}(b_1), \dots, \mathrm{bit}(b_k)$
on top of $R$ and side stack $U$ to label $w_n$, local variable $v'$, token stack $R$ and side
stack $\mathrm{bit}(b_k), \dots, \mathrm{bit}(b_1)$ on top of $U$.
