# Input head move of the clocked evaluator

For an input of length $n$, a shifted input head
position $p$ and a coded move $m$, the new position is $p - 1$ (truncated at $0$) if $m = 0$, $p$
if $m = 1$, and $\min(p + 1, n + 1)$ otherwise, so a move right never passes position $n + 1$,
one cell beyond the input.
