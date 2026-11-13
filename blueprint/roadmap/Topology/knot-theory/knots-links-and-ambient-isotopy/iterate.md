# Iterated braid-closure passes

For a braid word $w$, a number $f$ of remaining passes and
a traversal state $S$, the iteration returns $S$ when $f = 0$. When $f > 0$ it applies one pass
of $w$ to $S$, obtaining a state $S'$; it returns $S'$ if the strand position of $S'$ is $1$, and
otherwise iterates on $S'$ with $f - 1$ passes remaining.

The bound $f$ guarantees termination. The braid closure on $n$ strands uses $f = n$, since at
most $n$ distinct strand positions are visited.
