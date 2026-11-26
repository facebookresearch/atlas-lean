# Frame counter yields the number of raw frames in unary

Let $p^1, \ldots, p^k$ be bit strings, $x$ the concatenation of their framed forms, $c$ a bit string and $v$ a
Boolean. Started at label loop with internal state $v$, input $x$, empty scratch stack and counter $c$, the [frame
counter](prog.md) reaches label good with internal state $0$ (false), empty input and scratch stacks and counter
$1^k c$ in at most $4|x| + 1$ steps.
