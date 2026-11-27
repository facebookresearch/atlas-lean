# One Horner round

Let $b, \mathit{acc}, q, d, t$ be pairwise distinct counters of a
counter machine $M$, let $a \in \mathbb{N}$, let $\mu$ assign a label to each Horner-round stage
and let $\nu$ be a label. Suppose that for every Horner-round stage $s$ the label $\mu(s)$ runs
the Horner-round statement for $b, \mathit{acc}, q, d, t, a$ with stage labels $\mu$ and exit
label $\nu$ at stage $s$. Let $F$ be counter values with $F(q) = F(d) = F(t) = 0$, let $v$ be a
flag and $o$ an output, and let $h$ be the step count of one Horner round. Then $M$ runs from the
first multiplication stage $\mu(\mathrm{mul\ head})$ with flag $v$, counters $F$ and output $o$
in exactly $h(F(\mathit{acc}), F(b))$ steps to the label $\nu$ with flag false, output $o$, and
counters $F$ except that $\mathit{acc}$ holds $F(\mathit{acc}) \cdot F(b) + a$.
