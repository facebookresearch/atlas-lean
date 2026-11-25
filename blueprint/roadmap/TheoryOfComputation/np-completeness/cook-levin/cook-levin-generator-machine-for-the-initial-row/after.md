# Label after a literal routine (initial-row generator)

Let $g, n \in \mathbb{N}$, let $c$
be a clause kind of the generator with parameters $g$ and $n$, and let $l \in \mathbb{N}$. If
$l = 0$, the label is the final routine of $c$, which emits the leading gap. If $l \ge 1$, it is
the start of the routine for literal $l - 1$ of $c$ when $l - 1 < n + 2$, and the halting label
otherwise. The generator goes here after the routine for literal $l$, and with $l$ the number
of literals of $c$ before its first literal routine, so literals are emitted from the last to
the first.
