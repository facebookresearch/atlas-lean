# One step of the clause-length walk on a token

Let $\mathrm{cap}$ be a Boolean,
$n \in \mathbb{N}$, $s$ a token (a name bit, a polarity marker or the clause marker), $R$ and $U$
lists of symbols and $v$ a Boolean; stacks are lists written top first, and $w_m$ is the walking
label after $m$ literals. Let $t$ be $w_0$ if $s$ is the clause marker, $w_n$ if $s$ is a name
bit, and, if $s$ is a polarity marker, $\mathrm{fail}$ when $\mathrm{cap}$ is true and $n \ge 3$
and $w_{n+1}$ otherwise. The clause-length filter with cap flag $\mathrm{cap}$ goes in exactly
one step from label $w_n$, local variable $v$, token stack $s$ on top of $R$ and side stack $U$
to label $t$, local variable true, token stack $R$ and side stack $s$ on top of $U$.
