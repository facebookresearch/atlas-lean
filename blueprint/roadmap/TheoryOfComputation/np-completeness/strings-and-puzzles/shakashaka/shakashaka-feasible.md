# Feasible instances of SHAKASHAKA

An instance of SHAKASHAKA is feasible when there are options $s(r, c) \in \{0, 1, 2, 3, 4\}$ for the squares (only the options of white squares matter; option $0$ leaves a square white and options $1$ to $4$ make it a b/w square) such that, with $m$ the number of rows and $n$ the length of the first row:

- every square $(r, c)$ with $r < m$, $c < n$ and [entry](cell.md) $2 + i$ has exactly $i$ b/w squares among its neighbors, where a neighbor is one of the at most four squares of the $m \times n$ rectangle sharing a side with $(r, c)$, and it is a b/w square when its entry is $0$ and its option is not $0$;
- every connected component of the **interior of the union** of the closed white parts, that is, of the interior of the [white set](white-set.md), is an open axis-parallel rectangle $\{a_1 < x < a_2,\ b_1 < y < b_2\}$ or an open $45^\circ$ rectangle $\{a_1 < x + y < a_2,\ b_1 < x - y < b_2\}$.

The interior is taken after the union. Two white squares that meet only at a corner, such as the two white squares of the board $[[0, 1], [1, 0]]$ left with option $0$, lie in two different components (two open unit squares), so that board passes; two white squares sharing a side lie in one component, an open $1 \times 2$ rectangle. Feasibility does not include well-formedness; the decision problem requires both.
