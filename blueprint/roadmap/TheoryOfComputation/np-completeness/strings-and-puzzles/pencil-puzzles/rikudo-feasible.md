# Feasible instances of RIKUDO

An instance $(\tau, m, a)$ of RIKUDO, with $\tau$ a list of $n$ hexagonal cells, a list $m$ of placed numbers $(c, k)$ and a list $a$ of given adjacencies, is feasible when some numbering $s$ of the cells is a bijection from the cells of $\tau$ onto $\{1, \dots, n\}$ such that

- any two cells $c, d$ of $\tau$ with $s(c) + 1 = s(d)$ share an edge;
- $s(c) = k$ for every placed number $(c, k)$ in $m$; and
- the two cells of every given adjacency $(c, d)$ in $a$ have consecutive numbers: $s(c) + 1 = s(d)$ or $s(d) + 1 = s(c)$.
