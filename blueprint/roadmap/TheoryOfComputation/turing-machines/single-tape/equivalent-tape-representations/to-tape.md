# Post–Turing reading of a tape over the non-blank symbols

Let $\Gamma_0$ be an alphabet
whose default symbol is the blank. The Post–Turing reading of a two-way tape $t$ whose cells are
blank or hold non-blank symbols of $\Gamma_0$ is the Post–Turing machine tape over $\Gamma_0$
obtained cell by cell: take the view of $t$ as a tape of cells, each cell at its position relative
to the head and blank cells past the ends, and replace each cell by its symbol, a non-blank symbol
$x$ by $x$ itself and the blank cell by the blank of $\Gamma_0$.
