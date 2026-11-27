# One-hot generator: the label after a clause

Let $c$ be a clause kind of a cell with $g$
symbol codes: the at-least-one clause, or the at-most-one clause $\mathrm{amo}(x, y)$ for symbol
codes $x, y < g$. The label the generator goes to after clause $c$ is the end of the cell if $c$
is the at-least-one clause. If $c = \mathrm{amo}(x, y)$ with $x > 0$, it is the start of clause
$\mathrm{amo}(x - 1, y)$ when $x - 1 < y < g$, and the halting label otherwise. If
$c = \mathrm{amo}(0, y)$, it is the start of the at-least-one clause when $y \le 1$, and the start
of clause $\mathrm{amo}(y - 2, y - 1)$ when $y \ge 2$.
