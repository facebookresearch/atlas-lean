# Run of the literal routines of a clause (initial-row generator)

Let $c$ be a clause
kind with $k$ literals at base $B$, the $j$-th at position $B + \mathrm{off}(j)$, such that the
offsets are strictly increasing and every position is below $V$. For $l \le k$ let $b_l$ be
$B + \mathrm{off}(l)$ if $l < k$ and $V$ otherwise, let $\lambda_l$ be the list of literals of
$c$ (position and sign) from index $l$ on, and let the label before literal $l$ be the first
stage of the routine for literal $l - 1$, or the leading-gap stage of $c$ if $l = 0$. Write
$E(a, \lambda)$ for the gap encoding of the slots $a, \dots, V - 1$ with literals $\lambda$. Let
$F$ be counter values whose scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are
$0$ and whose base counter for $c$ equals $B$, and let $o$ be an output. Then for every $l \le k$
and flag $v$ there is a flag $v'$ such that the counter program runs in at most
$b_l(3V + 6) + l(6V + 9)$ steps from the label before literal $l$, with flag $v$, counters $F$
except $P = b_l$ and output $E(b_l, \lambda_l) \cdot 00 \cdot o$, to the leading-gap stage of
$c$, with flag $v'$, counters $F$ except $P = b_0$ and output $E(b_0, \lambda_0) \cdot 00 \cdot o$.
