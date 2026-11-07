# One step of the Thompson state count

Let $c = (c_0, \dots, c_{m-1})$ be a list of
natural numbers, and read $c_i$ as $0$ when $i \ge m$. The Thompson state count of a
regular-expression node from $c$ is $0$ for the node $0$, $1$ for the node $\varepsilon$, $2$ for
a letter, $c_i + c_j$ for a sum node and for a concatenation node with arguments $i$ and $j$, and
$c_i + 1$ for a star node with argument $i$.

When $c$ holds the counts of the nodes before the node, this is the number of states of
Thompson's automaton of its expression; an argument that is not an earlier node counts $0$, as
the expression $0$ does.
