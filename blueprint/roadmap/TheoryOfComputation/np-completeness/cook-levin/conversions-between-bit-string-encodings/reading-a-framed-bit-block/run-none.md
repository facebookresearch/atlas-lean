# Framed block reader fails on truncated framing

Let $M$, $a \ne b$, $d$, $g$, self, good, bad and $g_a$ be as in [reading a complete framed
block](run-delimit.md): the statement of $M$ at label self is the [framed-pair reading step](read.md) and
$d(g_a(c)) = c$ for each bit $c$.

Stack contents are listed from the top. Let $x$ be a bit string no prefix of which is the framed form $1 p_1 \cdots 1 p_m 0$ of a bit string $p$. Let
$v$ be a Boolean and $S$ stack contents such that stack $a$ holds exactly $g_a$ applied letter by letter to $x$.
Then there are an internal state $v'$ and stack contents $S'$ such that $M$ goes from label self, internal state
$v$ and stacks $S$ to label bad, internal state $v'$ and stacks $S'$ in at most $|x| + 1$ steps.

On failure stack $b$ may hold part of the payload.
