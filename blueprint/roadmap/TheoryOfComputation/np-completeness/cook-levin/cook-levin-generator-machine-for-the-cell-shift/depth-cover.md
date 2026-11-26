# Coverage of target depths

Let $p, c, H$ be natural numbers with $p \le H$ and $c \le H$,
and let $m = \max(p, c)$. Every natural number $j < H$ satisfies $j < p$, or $j = u + p$ for some
natural number $u < H - m$, or $j = H - c + p + r$ for some natural number $r < c - p$, where
$c - p$ is truncated subtraction (zero when $c \le p$).

In the cell-shift family these are the pushed-fill, in-range and overflow target depths of a
stack in the row after a time step.
