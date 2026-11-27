# Run of one literal routine (one-hot generator)

Let $L$ be a layout with $g$ symbol
codes, let $c$ be a clause kind of a cell with $g$ symbol codes, let $l < g$ be a literal index
with offset $\mathrm{off}_c(l)$, and let $F$ be counter values of the one-hot generator whose
scratch counters $Q$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$. Let
$q, \gamma \in \mathbb{N}$ with $q = F(\mathrm{CB}) + \mathrm{off}_c(l)$ and
$F(P) = q + \gamma + 1$. Then for every output $o$ and flag $v$, the one-hot generator for $L$
runs in at most $\gamma(3q + 6) + 2F(\mathrm{CB}) + 4q + 9$ steps from the first stage of the
routine for literal $l$ of $c$, with flag $v$, counters $F$ and output $o$, to the label after
literal $l$ of $c$ (the routine for literal $l - 1$, or the final stage of $c$ if $l = 0$), with
flag false, counters $F$ except $P = q$, and output $s \cdot (01)^{\gamma} \cdot o$, where $s$ is
the two-bit slot code of the sign of $c$ ($10$ if positive, $11$ if negative).
