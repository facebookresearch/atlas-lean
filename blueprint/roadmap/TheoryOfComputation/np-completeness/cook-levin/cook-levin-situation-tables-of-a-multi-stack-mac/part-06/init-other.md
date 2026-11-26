# Empty-stack clauses of the init family

Let $E$ be an encoding of a machine $M$ with $K$
numbered stacks and let $T, H$ be natural numbers. The empty-stack clauses form the CNF formula
that lists, for each stack number $k < K$ other than the number of the input stack in increasing
order and, within it, each depth $j < H$ in increasing order, the dense clause over the
$(T + 1)W$ variables of the layout of $E$, where $W$ is its row width at height $H$, whose only
literal is the positive literal of the cell variable of row $0$ for stack $k$, depth $j$ and code
$0$, the empty cell. They ask that every stack other than the input stack be empty in row $0$.
