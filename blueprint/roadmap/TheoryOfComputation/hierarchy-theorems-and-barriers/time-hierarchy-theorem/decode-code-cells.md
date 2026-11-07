# Decoding a code stack

For a bit list $x$, the decoding of $x$ as a code is defined as
follows. Write the cell of a number $n$ for the $n$ bits true followed by one bit false, and the
cells of a list of numbers for the cells of its numbers in order. If $x$ is the cells of a list
$l$ of natural numbers (such an $l$ is unique), the length of $l$ is a multiple of $4$, and the
keys $(q, a)$ of the entries $(q, a, q', s)$ formed by the consecutive groups of four numbers of
$l$ strictly increase in lexicographic order, then the decoding of $x$ is the code of these
entries. Otherwise the decoding returns no code.

The code stack of a code is the cells of the numbers $q, a, q', s$ of its entries
$(q, a, q', s)$, listed by increasing key $(q, a)$; codes with the same code stack have the same
clocked evaluator.
