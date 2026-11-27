# Literals of a one-hot clause kind

For a cell base $B$ and a clause kind $c$ of a cell
with $g$ symbol codes, the literals of $c$ form a list of pairs (variable, sign): for the
at-least-one kind, the pairs $(B + x, \mathrm{true})$ for $x = 0, \dots, g - 1$ in increasing
order; for the at-most-one kind of the pair $(x, y)$, the two pairs $(B + x, \mathrm{false})$
and $(B + y, \mathrm{false})$.
