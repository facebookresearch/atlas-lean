# The literal routine of the initial-row generator

For a clause kind $c$ and a literal
index $l < n + 2$, where $n$ is the number of certificate codes, the counter program at the
stages of the routine for literal $l$ of $c$. It copies the base counter of $c$ into the counter
$Q$ (restoring the base counter through a scratch counter) and adds the offset of literal $l$ to
$Q$. It then repeats: pop a unit from the counter $P$ (halting if $P$ is empty) and compare $P$
with $Q$, restoring both. If they are equal, it prepends the slot code of the sign of literal $l$
to the output, empties $Q$ and goes to the label before literal $l$: the routine for literal
$l - 1$, or the leading gap of the clause if $l = 0$. Otherwise it prepends the gap code $01$ to
the output and repeats.
