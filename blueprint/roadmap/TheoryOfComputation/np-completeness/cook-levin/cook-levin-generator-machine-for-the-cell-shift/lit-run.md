# One literal routine of the cell-shift generator

Let $i < N$ be a situation, $k < K$ a
stack, $c$ a clause kind and $l < 3$ a literal index. Let $F$ be counter values whose scratch
counters ($Q$, the copy buffer, the multiplication buffer and the two comparison buffers) are
$0$, let $b$ be the value under $F$ of the base counter of literal $l$, and let $a$ be the
constant offset of literal $l$ of $c$ in block $(i, k)$. Let $q, m \in \mathbb{N}$ satisfy
$q = b + a$ and $F(P) = q + m + 1$. Then for every output $o$ and internal state $v$, the
generator goes in at most $m(3q + 6) + 2b + 4q + 9$ steps from the start of the routine of
literal $l$, with state $v$, counters $F$ and output $o$, to the start of the routine of literal
$l - 1$ (the end-of-clause label of $c$ when $l = 0$), with state false, counters $F$ except
that $P = q$, and output the slot code of literal $l$ (sign positive exactly when $l$ is the last
literal of $c$), followed by $m$ copies of $01$, followed by $o$.
