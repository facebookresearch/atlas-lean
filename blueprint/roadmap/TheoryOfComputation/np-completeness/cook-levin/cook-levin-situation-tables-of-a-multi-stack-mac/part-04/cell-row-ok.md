# C1c (cell arrays of good configurations are well-formed rows)

Let $E$ be an encoding
of a machine $M$ with $K$ numbered stacks, and let $c$ be a good configuration of $M$, that is,
every symbol on every stack of $c$ lies in the effective alphabet of $E$. Let $w$ be the cell
array of $c$: $w(k, j)$ is the code of the symbol at depth $j$ from the top of stack number $k$,
or $0$ if there is none. Then for every $H \in \mathbb{N}$, $w$ is a well-formed row of height
$H$: for all $k < K$ and $j < H$, the code $w(k, j)$ is at most the size of the effective
alphabet of stack number $k$, and if $w(k, j) = 0$ then $w(k, b) = 0$ for every $b$ with
$j \le b < H$.
