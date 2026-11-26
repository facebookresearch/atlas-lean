# Run of one literal routine (initial-row generator)

For a layout and a list of $n$
certificate codes, let $c$ be a clause kind with base counter $b$, let $l < n + 2$ be a literal
index with offset $\mathrm{off}(l)$, and let $F$ be counter values whose scratch counters $Q$,
$\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$. Let $\gamma \in \mathbb{N}$, let
$q = F(b) + \mathrm{off}(l)$ and suppose $F(P) = q + \gamma + 1$. Then for every output $o$ and
flag $v$, the counter program runs in at most $\gamma(3q + 6) + 2F(b) + 4q + 9$ steps from the
first stage of the routine for literal $l$ of $c$, with flag $v$, counters $F$ and output $o$, to
the label before literal $l$ (the routine for literal $l - 1$, or the leading gap if $l = 0$),
with flag false, counters $F$ except $P = q$, and output $s \cdot (01)^{\gamma} \cdot o$, where
$s$ is the slot code of the sign of literal $l$.
