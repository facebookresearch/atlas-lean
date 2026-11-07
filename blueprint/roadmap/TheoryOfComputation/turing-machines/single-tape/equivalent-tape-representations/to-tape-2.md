# Cell view of a two-way tape

A CSLib tape $t$ over an alphabet $\Gamma$ has a head cell
and two halves, each a finite list of cells not ending in a blank, where a cell is a symbol of
$\Gamma$ or the blank. Its cell view is the Mathlib tape over cells, with the blank as default
symbol, whose head is the head cell of $t$ and whose left and right halves are the halves of $t$,
blank past their ends. So the cell at position $i \in \mathbb{Z}$ of the view is the cell $i$
places to the right of the head of $t$ (to the left when $i < 0$).
