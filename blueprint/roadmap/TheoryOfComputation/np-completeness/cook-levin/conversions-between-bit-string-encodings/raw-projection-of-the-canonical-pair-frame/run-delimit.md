# Pair-frame splitter extracts both raw fields

Let $p$, $r$ and $o$ be bit strings and $v$ a Boolean, and let $f(p) = 1 p_1 \cdots 1 p_m 0$ be the framed form of
$p$. There is an internal state $v'$ such that the [pair-frame splitter](prog.md) goes from label read, internal
state $v$, input $f(p) r$, left stack $o$ and empty scratch stack to label good, internal state $v'$, input $r$,
left stack $p o$ and empty scratch stack in exactly $2|p| + 2$ steps. (Stack contents are listed from the top.)
