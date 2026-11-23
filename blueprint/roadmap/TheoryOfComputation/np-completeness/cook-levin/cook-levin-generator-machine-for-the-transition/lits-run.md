# Run of the literal routines of a clause (transition-clause generator)

Let $t < T$, let
the tables be well formed for situation $i < N$ at height $H$, and let $F$ be a counter assignment
resting at time $t$: its scratch counters $Q$, $\mathrm{Ka}$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$,
$c_2$ are $0$, $F(\mathrm{TW}) = tW$, $F(\mathrm{HG}) = Hg$, $F(\mathrm{Wc}) = W$ and
$F(\mathrm{Vc}) = V$, where $g$ is the number of symbol codes of the layout, $W$ is the number of
variables per time step and $V = (T + 1)W$. Let $n$ be the number of literals of a clause. For
$j \le n$ let $b_j$ be the position of literal $j$ of clause $(t, i)$ when $j < n$, and $b_n = V$;
let $e_j$ be the gap encoding of the slots $b_j, \dots, V - 1$ whose literals are those of clause
$(t, i)$ numbered $j$ or more. Then for every output $o$, every $j \le n$ and every state $v$
there is a state $v'$ such that the generator runs in at most $b_j(3V + 6) + jE$ steps, where $E$
is the per-literal time bound, from the label that follows literal $j$ with state $v$, counters
$F$ except that $P = b_j$, and output $e_j\,00\,o$, to the leading-gap stage of situation $i$
with state $v'$, counters $F$ except that $P = b_0$, and output $e_0\,00\,o$.

The label that follows literal $j$ is the routine for literal $j - 1$, or the leading-gap stage
when $j = 0$.
