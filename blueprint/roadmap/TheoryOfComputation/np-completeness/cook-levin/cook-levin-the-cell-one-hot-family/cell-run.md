# Generator run for one cell

Let $L$ be a layout with $g$ symbol codes and let $j < H$, $V$
and $B$ be natural numbers. Let $F$ be counter values of the one-hot generator with the scratch
counters $Q$, tmp, md, $c_1$, $c_2$ empty, the counters $CB$ and $P$ zero, $Vc = V$, $Gc = g$,
$Hs = j$, $j g + KB = B$, and suppose $B + g \le V$. Then for every output $o$ and flag $v$, the
generator goes, in at most the one-cell step bound for $g$, $H$, $V$ steps, from the start of the
body of the depth loop with flag $v$, counters $F$ and output $o$ to the head of the depth loop
with flag false, counters $F$ and output the encoding of the one-hot clauses of the cell with
base $B$ over $V$ variables followed by $o$.
