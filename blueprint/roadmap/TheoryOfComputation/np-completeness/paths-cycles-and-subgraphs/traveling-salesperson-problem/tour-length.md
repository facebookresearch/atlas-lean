# Length of a tour in the symmetric TSP

Let $w$ be a matrix of natural numbers given as a
list of rows, where an entry $w_{a,b}$ outside the list (no row $a$, or row $a$ too short) is
read as $0$, and rows and columns are numbered from $0$. The length of a list
$(t_0, \dots, t_{k-1})$ of natural numbers with respect to $w$ is
$\sum_{j\lt k} w_{t_j, t_{(j+1) \bmod k}}$, the total weight of the edges along the cycle
$t_0, t_1, \dots, t_{k-1}, t_0$, including the return edge; the empty list has length $0$.
