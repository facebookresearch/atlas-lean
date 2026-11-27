# Stacks of height at most one give a one-cell tape

Let $M$ be a finite multi-stack
machine, and let $S$ assign to every stack $k$ of $M$ a list $S_k$ of length at most $1$. Let $L'$
be a tape of stack columns whose $k$-th track, for every $k$, is $S_k$ laid out bottom first and
followed by blanks. Then adding the bottom marker to $L'$, as in the translation of $M$ to a
single-tape machine, gives the tape whose first cell is flagged as the bottom and holds the top of
$S_k$ on every stack $k$ (nothing if $S_k$ is empty), followed by blank cells.
