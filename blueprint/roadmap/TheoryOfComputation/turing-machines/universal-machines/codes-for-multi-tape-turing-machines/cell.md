# Cell of a zipper tape

For a work tape $t$ in zipper form and an integer $j$, the cell of
$t$ at $j$ is the symbol at offset $j$ from the head: for $j = n \ge 0$ it is entry $n$ (counting
from $0$) of the list of cells from the head rightwards, and for $j = -(n + 1)$ it is entry $n$ of
the list of cells left of the head, nearest first; in either case it is the blank when the list
has no entry $n$.
