# One frame adds one unary count bit

Let $p$, $x$ and $c$ be bit strings and $v$ a Boolean, and let $f$ be the framed form $1 p_1 \cdots 1 p_m 0$ of
$p$. Started at label loop with internal state $v$, input $fx$, empty scratch stack and counter $c$, the [frame
counter](prog.md) reaches label loop with internal state $0$ (false), input $x$, empty scratch stack and counter
$1c$ in at most $4|f| = 8|p| + 4$ steps. (Stack contents are listed from the top.)
