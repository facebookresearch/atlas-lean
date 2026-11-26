# The literal routines of one clause of the cell-shift generator

Fix $V \in \mathbb{N}$, a
situation $i < N$, a stack $k < K$, a clause kind $c$ with $n$ literals, positions
$p : \mathbb{N} \to \mathbb{N}$, counter values $F$ whose scratch counters are $0$, and an output
$o$. Suppose that for every $l$ the position $p(l)$ is the value under $F$ of the base counter of
literal $l$ plus its constant offset in block $(i, k)$, that this base value is at most $V$, that
$p(l) < p(l + 1)$ whenever $l + 1 < n$, and that $p(n - 1) < V$ if $n \ge 1$. Let
$\beta(l) = p(l)$ for $l < n$ and $\beta(l) = V$ otherwise, and let $E(l)$ be the gap encoding,
from slot $\beta(l)$ up to $V$, of literals $l, \dots, n - 1$ of $c$ at positions $p$, each
with sign positive exactly when it is the last literal. Then for every $l \le n$ and every
internal state $v$ there is a state $v'$ such that the generator goes in at most
$\beta(l)(3V + 6) + l(6V + 9)$ steps from the start of the routine of literal $l - 1$ (the
end-of-clause label of $c$ when $l = 0$), with state $v$, counters $F$ except that
$P = \beta(l)$, and output $E(l)$ followed by $00$ and $o$, to the end-of-clause label of $c$,
with state $v'$, counters $F$ except that $P = \beta(0)$, and output $E(0)$ followed by $00$
and $o$.
