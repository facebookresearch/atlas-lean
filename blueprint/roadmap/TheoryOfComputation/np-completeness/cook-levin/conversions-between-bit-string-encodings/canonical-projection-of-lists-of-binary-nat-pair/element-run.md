# Pair-list projector emits one weight and one value frame per item

Stack contents are listed from the top; $f(p)$ is the framed form $1 p_1 \cdots 1 p_k 0$ of a bit string $p$ and
$c(m)$ the binary code of $m$. Let $p$ be a bit string on which the [decoder of pairs of natural
numbers](../projecting-and-normalizing-a-pair-of-binary-natu/decode-pair-nat.md) returns $(m, n)$, let $r$, $a_1$,
$a_2$, $o_1$, $o_2$ be bit strings and $v$ a Boolean. Started at label loop with internal state $v$, input $f(p) r$,
accumulators $a_1, a_2$, outputs $o_1, o_2$ and empty workspace, the [pair-list projector](prog.md) reaches label
loop with internal state $0$ (false), input $r$, first accumulator $f(c(m))$ reversed followed by $a_1$, second
accumulator $f(c(n))$ reversed followed by $a_2$, outputs $o_1, o_2$ and empty workspace in at most $12|f(p)|$
steps.
