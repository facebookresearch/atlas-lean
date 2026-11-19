# Decoding a list of cells

For a bit list $x$, the list of natural numbers $l$ whose
cells are $x$, if there is one, and nothing otherwise. Here the cells of $l$ are its numbers
written in order, each number $n$ as $n$ copies of $\mathrm{true}$ followed by one
$\mathrm{false}$; distinct lists have distinct cells. The decoder reads one cell at a time
with the unary length reader.
