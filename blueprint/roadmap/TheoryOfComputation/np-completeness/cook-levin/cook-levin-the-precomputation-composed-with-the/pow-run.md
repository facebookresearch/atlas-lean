# The power loop

Let $b, k, p, q, a, t$ be pairwise distinct counters of a counter machine
$M$, let $\mu$ assign a label to each power-loop stage and let $\nu$ be a label. Suppose that for
every power-loop stage $s$ the label $\mu(s)$ runs the power-loop program for $b, k, p, q, a, t$
with stage labels $\mu$ and exit label $\nu$ at stage $s$. Let $j \in \mathbb{N}$, let $F$ be
counter values with $F(k) = j$ and $F(q) = F(a) = F(t) = 0$, let $v$ be a flag and $o$ an
output. Then $M$ runs from the head stage $\mu(\mathrm{hd})$ with flag $v$, counters $F$ and
output $o$ to the label $\nu$ with flag false, output $o$, and counters $F$ except that $p$ holds
$F(p) \cdot F(b)^j$ and $k$ holds $0$, within $j\,(F(p)\,(F(b) + 1)^j\,(3F(b) + 5) + 5) + 1$
steps, the step budget of the power loop for $j$ rounds, start value $F(p)$ and base $F(b)$.
