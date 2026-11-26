# Input clauses of the init family

Let $E$ be an encoding of a machine $M$, let
$x = x_0 x_1 \cdots x_{n-1}$ be a list of symbols of the input stack of $M$, and let $T, H$ be
natural numbers. The input clauses form the CNF formula that lists, for $j = 0, 1, \dots, n - 1$
in order, the dense clause over the $(T + 1)W$ variables of the layout of $E$, where $W$ is its
row width at height $H$, whose only literal is the positive literal of the cell variable of row
$0$ for the input stack, depth $j$ and the symbol code under $E$ of $x_j$. They pin the input $x$
at the top of the input stack, one cell at a time.
