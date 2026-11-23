# Number-pair projector reaches the decoding outcome

Let $x$ be a bit string and $v$ a Boolean. There are an internal state $v'$ and stack contents $S$ such that the
[number-pair projector](prog.md), started at label $\mathrm{pair}(\mathrm{read})$ with internal state $v$, splitter
input $x$ and all other stacks empty, reaches in at most $2|x| + 6$ steps, with internal state $v'$ and stacks $S$,
the label good if the [decoder of pairs of natural numbers](decode-pair-nat.md) succeeds on $x$ and bad if it fails;
moreover, if it returns $(m, n)$, then in $S$ the left output holds the binary code of $m$, the right output the
binary code of $n$, and every other stack is empty.
