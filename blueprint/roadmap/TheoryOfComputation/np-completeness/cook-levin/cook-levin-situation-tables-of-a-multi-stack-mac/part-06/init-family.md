# The row-0 init family of an encoding

Let $E$ be an encoding of a machine $M$, let $x$ and
$Y$ be lists of symbols of the input stack of $M$, and let $m, T, H$ be natural numbers. The init
family is the CNF formula whose clauses are, in this order, those of the start-code clause at
$(T, H)$, the empty-stack clauses at $(T, H)$, the input clauses of $x$ at $(T, H)$, the
certificate clauses of $x$ and $Y$ at $(m, T, H)$, the prefix clauses of $x$ at $(m, T, H)$ and
the tail clauses at $(m, T, H)$.

Together they ask that row $0$ hold the start code, empty stacks other than the input stack, the
input $x$ at the top of the input stack, cells that are empty or hold a symbol of $Y$ at the
depths $|x| \le j < m$, with an empty cell at such a depth $j$ forcing an empty cell at $j + 1$,
and empty cells at the depths $m \le j < H$.
