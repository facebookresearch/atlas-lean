# Feasible Minesweeper instances

Index rows and columns by natural numbers, and call a cell
$(r', c') \ne (r, c)$ a neighbour of $(r, c)$ when $|r' - r| \le 1$ and $|c' - c| \le 1$. A
Minesweeper instance with $R$ rows, $C$ columns and a list of clues is feasible when there is a
finite set $M$ of cells $(r, c)$ with $r < R$ and $c < C$ (the mines) such that for every clue
$(r, c, k)$ in the list the cell $(r, c)$ is not in $M$ and exactly $k$ cells of $M$ are
neighbours of $(r, c)$.
