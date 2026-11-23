# Pair-frame splitter reaches the framing outcome

Let $x$ be a bit string and $v$ a Boolean. There are an internal state $v'$ and stack contents $S$ such that the
[pair-frame splitter](prog.md), started at label read with internal state $v$, input $x$ and empty left and scratch
stacks, reaches in at most $|x| + 1$ steps, with internal state $v'$ and stacks $S$, the label good if some prefix
of $x$ is the framed form of a bit string and the label bad otherwise; moreover, if $x$ is the framed form of $p$
followed by $r$, then $S$ has input $r$, left stack $p$ and an empty scratch stack.
