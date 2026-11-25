# Half-tape view of a stack tape

A stack tape $s$ over an alphabet $\Gamma$ is a finite list
of cells, each a symbol of $\Gamma$ or the blank cell, that does not end in a blank cell. Its
half-tape view is the half-tape of cells (a sequence of cells taken up to trailing blanks, the
blank cell being the default) whose cells are those of $s$ in order, followed by blank cells.
