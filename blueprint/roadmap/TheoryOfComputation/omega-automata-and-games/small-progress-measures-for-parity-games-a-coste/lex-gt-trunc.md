# Strict truncated lexicographic order

For a threshold $p$ and tuples $a, b$ of $d + 1$ natural numbers with indices $0, \dots, d$, $a >_p b$ holds when there is an index $j \ge p$ with $a_j > b_j$ and $a_i = b_i$ for every $i > j$: scanning the components from index $d$ down to $p$, the first one where $a$ and $b$ differ has $a$ larger. Components below $p$ are ignored. It compares suffixes, from the top index down. Jurdziński's paper instead compares prefixes, under the convention that the least priority occurring infinitely often decides the winner; this page uses the reversed convention.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
