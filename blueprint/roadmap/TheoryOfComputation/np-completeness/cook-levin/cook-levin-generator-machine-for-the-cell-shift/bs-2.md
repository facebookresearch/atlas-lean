# Base counter of a literal

For a clause kind $c$ and $l \in \mathbb{N}$: if $c$ is an
in-range shift clause, literal $l$ has base $cb$ when $l = 0$, $s$ when $l = 1$ and $cw$ when
$l \ge 2$; if $c$ is an overflow or pushed-fill clause, it has base $s$ when $l = 0$ and $cw$
otherwise.
