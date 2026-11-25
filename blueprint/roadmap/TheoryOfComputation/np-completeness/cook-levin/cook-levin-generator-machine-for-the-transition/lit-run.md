# Run of one literal routine (transition-clause generator)

Let $i < N$ be a situation, $j$
less than the number of literals, and $F$ a counter assignment whose scratch counters $Q$,
$\mathrm{Ka}$, $\mathrm{tmp}$, $\mathrm{md}$, $c_1$, $c_2$ are $0$. Let
$q = F(\mathrm{TW}) + k_A(j) F(\mathrm{HG}) + k_B(j) F(\mathrm{Wc}) + c_i(j)$, where $k_A$, $k_B$
and $c_i(j)$ are the stack index, the row offset and the constant part of the position of literal
$j$, and suppose $F(P) = q + m + 1$ for a natural number $m$. Let $K$ be the number of stacks of
the layout. Then for every output $o$ and every state $v$, the generator runs in at most

$$m(3q + 6) + 2F(\mathrm{TW}) + K(2F(\mathrm{HG}) + 3) + 2K + 2F(\mathrm{Wc}) + 4q + 22$$

steps from the first stage of the routine for literal $j$ of situation $i$, with state $v$,
counters $F$ and output $o$, to the label that follows literal $j$, with state false, counters $F$
except that $P = q$, and output $s\,(01)^m\,o$, where $s$ is the slot code of a literal with
polarity $\mathrm{sgn}(j)$.
