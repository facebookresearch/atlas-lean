# Rows pushed for a clause's literals

For a list $I$ of items and literals
$l_1, \dots, l_k$, the rows are the concatenation, for $i = 1, \dots, k$ in turn, of the reverse
of the walk bits of $l_i$ with flag false over the items $l_{i+1}, \dots, l_k$ (as occurrence
items) followed by $I$. These are the bits pushed when the literals of a clause are walked above
the items $I$.
