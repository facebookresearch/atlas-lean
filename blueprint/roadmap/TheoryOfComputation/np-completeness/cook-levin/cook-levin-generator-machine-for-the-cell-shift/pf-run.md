# The pushed-fill chain of the cell-shift generator

Let $L$ be a layout with label block
size $A$, $K$ stacks and $g$ symbol codes, let $W = A + K H g$ be the row width and
$V = (T + 1) W$ the number of variables, and let the tables $s_a, p, c, p_u$ be well formed for
$N$ situations and height $H$. Let $t < T$, $i < N$, $k < K$, and let $F$ be counter values in
which $\mathrm{Q}$, $\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$ and $\mathrm{P}$
are $0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$, $F(\mathrm{TW}) = t W$,
$F(\mathrm{TW1}) = (t + 1) W$ and $F(\mathrm{CW}) = k H g + t W + A + W$. Then for every
$n \le p(i, k)$, every output word $o$ and every flag $v$ there is a flag $v'$ such that the
generator for these data, started at the entry label of the pushed-fill chain for $n$ in block
$(i, k)$ with flag $v$, counters $F$ and output $o$, reaches the fill-drain stage $\mathrm{fD1}$
of block $(i, k)$ (before draining) with flag $v'$, counters $F$ and output
$e_0 e_1 \cdots e_{n-1}$ followed by $o$ in at most $n \cdot \mathrm{clauseB}(V)$ steps, where
$\mathrm{clauseB}(V) = 3 V^2 + 27 V + 31$ and $e_j$ is the encoding of the dense clause over $V$
variables whose literals are those of the pushed-fill clause $(t, i, k, j)$.
