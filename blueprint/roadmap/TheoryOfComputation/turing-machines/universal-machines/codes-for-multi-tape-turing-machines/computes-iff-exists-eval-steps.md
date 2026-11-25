# A code computes exactly what its clocked evaluator returns

For a code $c$ with $k$ work
tapes and binary words $x$ and $o$, the machine of $c$ computes $o$ on input $x$, that is, it
eventually halts on $x$ with output $o$, if and only if there is a clock $T \in \mathbb{N}$ such
that the clocked evaluator of $c$ run on $x$ for $T$ steps returns $o$.
