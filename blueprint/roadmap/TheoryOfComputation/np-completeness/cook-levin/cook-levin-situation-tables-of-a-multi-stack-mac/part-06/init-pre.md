# Prefix clauses of the init family

Let $E$ be an encoding of a machine $M$, let $x$ be a
list of symbols of the input stack of $M$, and let $m, T, H$ be natural numbers. For a depth $j$,
write $Z_j$ for the cell variable of row $0$, input stack, depth $j$ and code $0$ (the empty cell)
in the layout of $E$ at height $H$. The prefix clauses form the CNF formula that lists, for
$j = |x|, |x| + 1, \dots, m - 1$ in order (none if $m \le |x|$), the dense clause over the
$(T + 1)W$ variables of the layout, where $W$ is its row width at height $H$, with the literals
$\neg Z_j$ and $Z_{j+1}$. On these depths, an empty cell forces an empty cell one level deeper.
