# Mismatches

The distance $d(X, Y)$ between a fragment row $X$ of natural numbers and a haplotype $Y \in \{0, 1\}^m$: the number of positions $j < m$ at which the entry $x$ of $X$ is not $2$ and the truth value of $x = 1$ differs from $Y_j$. A position beyond the row's length is read as $2$ (a hole), and holes do not count. Every other entry is read as $1$ (true) when it equals $1$ and as $0$ (false) otherwise, so an entry above $2$ counts like $0$; on a [well-formed](well-formed.md) row, whose entries are $0$, $1$ or $2$, this is the number of $0$/$1$ entries that differ from $Y$.
