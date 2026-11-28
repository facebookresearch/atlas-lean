# ZEIGER instance encoding

A ZEIGER instance is a finite list of rows, each row a finite list of cells, and each cell a pair $(d, a) \in \mathbb{N} \times \mathbb{N}$. The first component $d$ encodes the arrow of the cell: $d = 0$ is up, $d = 1$ right, $d = 2$ down and $d = 3$ left. The second component is $a = 0$ when the cell carries no number, and otherwise it is the integer $a$ given in that cell.

Nothing in the type forces the rows to have equal length or $d < 4$; those conditions are part of well-formedness.
