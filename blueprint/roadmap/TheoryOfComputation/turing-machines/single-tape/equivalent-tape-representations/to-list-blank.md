# Half-tape of a stack tape of non-blank symbols

Let $\Gamma_0$ be an alphabet with blank
symbol $b$ and $N = \Gamma_0 \setminus \{b\}$ its non-blank symbols. A stack tape $s$ over $N$, a
finite list of cells each blank or holding a symbol of $N$ and not ending in a blank cell, is read
as the TM0 half-tape over $\Gamma_0$ whose $i$-th symbol is that of the $i$-th cell of $s$: $b$
for a blank cell, $x$ for a cell holding $x$, and $b$ past the end of $s$.
