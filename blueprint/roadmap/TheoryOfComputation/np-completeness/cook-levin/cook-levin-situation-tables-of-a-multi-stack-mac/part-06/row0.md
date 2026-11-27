# Row-0 obligation

For an encoding $E$ of a machine $M$ with $K$ stacks, an assignment $a$, a
height $H$ and an input list $s$, let $c$ be the start configuration of $M$ on $s$. The row-0
obligation says that, in the layout of $E$ at height $H$, the literal of the (label, state) code
of $c$ in row $0$ is true under $a$ and, for every stack number $k < K$ and depth $j < H$, the
literal of the cell code of $c$ at stack $k$ and depth $j$ in row $0$ is true under $a$.

This is a positive form: the literals of the other cell codes are not required to be false.
