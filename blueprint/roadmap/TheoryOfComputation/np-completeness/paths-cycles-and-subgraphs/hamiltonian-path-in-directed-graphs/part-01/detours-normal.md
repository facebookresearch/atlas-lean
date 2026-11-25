# Normal clause detours

Let $\varphi$ be a CNF formula with $m$ clauses and $k$ distinct
variables, and write $R(i, l)$ for row vertex $l$ of diamond $i$ in the HAMPATH construction for
$\varphi$. A list of vertices $p$ has normal detours when for every clause $j < m$ there is a
diamond $i < k$ such that $p$ contains $R(i, 3j + 1), j, R(i, 3j + 2)$ or
$R(i, 3j + 2), j, R(i, 3j + 1)$ as consecutive entries.
