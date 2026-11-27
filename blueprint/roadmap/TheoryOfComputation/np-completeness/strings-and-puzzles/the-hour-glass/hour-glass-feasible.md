# Feasible THE HOUR-GLASS instances

A choice of one in-range column in each stored row whose entries sum to $t$. On a step from row $r$ to row $r + 1$, the next column is the same or one smaller if $r + 1 < m$, and the same or one larger otherwise, where $m$ is the declared turning row. With rows `[[0], [1, 0]]` and target zero, $m = 1$ works and $m = 2$ does not. With no rows the empty sum is zero, so feasibility holds exactly at $t = 0$. Diagonal motion on an hour-glass is the reading for validated input.
