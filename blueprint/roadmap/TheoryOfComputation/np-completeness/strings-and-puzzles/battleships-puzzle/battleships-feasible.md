# Feasible BATTLESHIPS instances

An instance $(R, C, F, G)$ of BATTLESHIPS is feasible when some list of ship placements satisfies: for every $k$, the number of placed ships of length $k + 1$ equals entry $k$ of $F$ ($0$ when $F$ has no entry $k$); every ship has positive length and lies inside the grid; a given cell is occupied exactly when its flag says it holds a ship segment; no two distinct ships have cells that are equal or adjacent, orthogonally or diagonally; and every row $r$ has exactly $R_r$ occupied cells and every column $c$ has exactly $C_c$ occupied cells.
