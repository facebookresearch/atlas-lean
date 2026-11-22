# Run of the literal routines of a clause (one-hot generator)

Let $L$ be a layout with $g$
symbol codes, let $c$ be a well-formed clause kind of a cell with $g$ symbol codes (the
at-least-one clause, or the at-most-one clause $\mathrm{amo}(x, y)$ with $x < y$) with $n$
literals, write $\mathrm{off}_c(l)$ for the offset of literal $l$ of $c$ from the cell base, and
let $B, V \in \mathbb{N}$ with $B + g \le V$. For $l \le n$ let $b_l$ be
$B + \mathrm{off}_c(l)$ if $l < n$ and $V$ otherwise, let $\lambda_l$ be the list of literals of
$c$ at base $B$ (position and sign) from index $l$ on, and let the label after literal $l$ be the
routine for literal $l - 1$ of $c$, or the final stage of $c$ if $l = 0$. Write $E(a, \lambda)$
for the gap encoding of $\lambda$ from slot $a$ to $V$. Let $F$ be counter values of the one-hot
generator whose scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$ and
with $F(\mathrm{CB}) = B$, and let $o$ be an output. Then for every $l \le n$ and flag $v$ there
is a flag $v'$ such that the one-hot generator for $L$ runs in at most $b_l(3V + 6) + l(6V + 9)$
steps from the label after literal $l$ of $c$, with flag $v$, counters $F$ except $P = b_l$ and
output $E(b_l, \lambda_l) \cdot 00 \cdot o$, to the final stage of $c$, with flag $v'$, counters
$F$ except $P = b_0$ and output $E(b_0, \lambda_0) \cdot 00 \cdot o$.
