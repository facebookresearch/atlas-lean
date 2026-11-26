# Entry label for the first rows of a cell

Let $g$ be the number of symbol codes of the
one-hot generator. For a natural number $y$, this is the label of the generator at which the
at-least-one clause starts when $y \le 1$; when $2 \le y \le g$, the label starting the
at-most-one clause for the pair $(y - 2, y - 1)$; and when $y \ge 2$ and $y > g$, the final
label $\mathrm{done}$.

From here, for $y \le g$, the generator emits the clauses of the rows below $y$, then the
at-least-one clause.
