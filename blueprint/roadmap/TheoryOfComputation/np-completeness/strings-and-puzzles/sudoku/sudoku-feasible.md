# Feasible Sudoku instances

A Sudoku instance $(n, G)$, with block size $n$ and grid $G$ a
list of rows of natural numbers, is feasible when there is a grid $C$ of natural numbers with
exactly $n^2$ rows, each of exactly $n^2$ entries, such that, indexing rows and columns from $0$:
for all $r, c < n^2$ the entry $G_{rc}$ is $0$ or equals $C_{rc}$, where an entry missing from
$G$ counts as $0$; every row of $C$ and every column of $C$ lists each of $1, \dots, n^2$ exactly
once; and for all $b, b' < n$ the $n^2$ entries $C_{bn + i,\, b'n + j}$ with $i, j < n$ list each
of $1, \dots, n^2$ exactly once.
