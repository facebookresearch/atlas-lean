# Mismatches

The distance $d(X, Y)$ between a fragment row $X$ and a haplotype $Y \in \{0, 1\}^m$: the number
of positions $j < m$ at which $X$ has a $0$ or $1$ entry different from $Y_j$. Holes (entry $2$)
do not count, and a position beyond the row's length is read as a hole.
