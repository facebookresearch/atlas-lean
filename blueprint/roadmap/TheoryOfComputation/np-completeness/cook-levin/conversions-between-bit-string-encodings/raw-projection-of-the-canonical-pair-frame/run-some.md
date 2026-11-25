# Pair-frame splitter projects every well-framed input in linear time

Let $x$, $p$, $r$ be bit strings such that $x$ is the framed form $1 p_1 \cdots 1 p_m 0$ of $p$ followed by $r$,
let $o$ be a bit string and $v$ a Boolean. There is an internal state $v'$ such that the [pair-frame
splitter](prog.md) goes from label read, internal state $v$, input $x$, left stack $o$ and empty scratch stack to
label good, internal state $v'$, input $r$, left stack $p o$ and empty scratch stack in at most $|x| + 1$ steps.
The fields $p$ and $r$ are not normalized.
