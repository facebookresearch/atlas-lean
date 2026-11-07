# Certificate clauses of the init family

Let $E$ be an encoding of a machine $M$, let $x$
and $Y$ be lists of symbols of the input stack of $M$, and let $m, T, H$ be natural numbers. For a
depth $j$ and a symbol code $c$, write $C_0[j, c]$ for the cell variable of row $0$, input stack,
depth $j$ and code $c$ in the layout of $E$ at height $H$, and let $e$ be the symbol code of $E$
on the input stack. The certificate clauses form the CNF formula that lists, for each depth
$j = |x|, |x| + 1, \dots, m - 1$ in order (none if $m \le |x|$), the dense clause over the
$(T + 1)W$ variables of the layout, where $W$ is its row width at height $H$, whose literals are
$C_0[j, 0]$ followed by $C_0[j, e(z)]$ for each $z$ in $Y$ in order, all positive.

Code $0$ is the empty cell, so the clause for $j$ asks that depth $j$ of the input stack be empty
or hold a symbol of $Y$.
