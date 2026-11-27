# One clause of the cell-shift generator

Let $M$ be the cell-shift generator for a layout
$L$ with $K$ stacks, $g$ symbol codes and window depth $d$, situation offsets $\mathrm{sa}$, push
counts $\mathrm{pl}$, consumed counts $\mathrm{cn}$, pushed codes $\mathrm{pu}$ and $N$
situations. Fix a situation $i < N$, a stack $k < K$, a clause kind $c$ with parameters $g$ and
$d$ and with $n$ literals, positions $\mathrm{pos} : \mathbb{N} \to \mathbb{N}$, counter values $F$
and $V \in \mathbb{N}$. For each $l \in \mathbb{N}$ let $b_l$ be the counter holding the base of
literal $l$ of $c$ and $o_l$ the constant offset of literal $l$ of $c$ in block $(i, k)$. Assume
that the scratch counters $\mathrm{Q}$, $\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$ and
$\mathrm{c2}$ are zero in $F$; that $\mathrm{pos}(l) = F(b_l) + o_l$ and $F(b_l) \le V$ for every
$l \in \mathbb{N}$; that $\mathrm{pos}(l) < \mathrm{pos}(l + 1)$ whenever $l + 1 < n$ and
$\mathrm{pos}(n - 1) < V$; and that $F(\mathrm{Vc}) = V$ and $F(\mathrm{P}) = 0$. Then for every
output word $w$ and flag $v$, $M$ runs in at most $V(3V + 6) + 3(6V + 9) + 3V + 4$ steps (the step
bound for one clause) from the configuration with label $\mathrm{e00}(c)$ of block $(i, k)$, flag
$v$, counter values $F$ and output $w$ to the configuration with the label that follows clause $c$
in block $(i, k)$, flag false, counter values $F$ and output $e$ followed by $w$, where $e$ is the
encoding of the dense clause over $V$ variables whose literals are those of $c$ at positions
$\mathrm{pos}$.
