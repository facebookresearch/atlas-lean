# Connectable points in GENERALIZED SHISEN-SHO

In GENERALIZED SHISEN-SHO, given a set of occupied integer points, two points $a$ and $b$ of $\mathbb{Z} \times \mathbb{Z}$ are connectable when there are points $p_1$ and $p_2$, ranging over **all** of $\mathbb{Z} \times \mathbb{Z}$ and not only over board cells, such that $a$ and $p_1$, $p_1$ and $p_2$, and $p_2$ and $b$ each share a row or a column, and no integer point other than $a$ and $b$ on the [segments](on-segment.md) from $a$ to $p_1$, from $p_1$ to $p_2$ and from $p_2$ to $b$ is occupied. Degenerate segments (with equal endpoints) are allowed, so adjacent points and paths of one or two segments also qualify.

For example, on the one-row board $[1, 2, 1, 2, 1, 2, 1, 2]$ with every cell occupied, the first two tiles labeled $1$, at $(0, 0)$ and $(0, 2)$, are connectable through $p_1 = (-1, 0)$ and $p_2 = (-1, 2)$, one row outside the board.
