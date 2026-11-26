# Strict truncated lexicographic order

For a threshold $p$ and tuples $a, b$ of $d + 1$ natural numbers with indices $0, \dots, d$, $a >_p b$ holds when there is an index $j \ge p$ with $a_j > b_j$ and $a_i = b_i$ for every $i > j$: scanning the components from index $d$ down to $p$, the first one where $a$ and $b$ differ has $a$ larger. Components below $p$ are ignored.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301.
