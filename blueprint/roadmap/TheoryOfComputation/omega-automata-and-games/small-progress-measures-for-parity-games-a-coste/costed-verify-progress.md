# The costed progress-measure verifier

For a parity game on $n$ positions and a partial assignment $\mu$ of tuples of $d + 1$ natural numbers to positions, the costed verifier computes the result of the progress-measure verifier together with the number of atomic comparisons it evaluates: one move test per pair of positions plus the atomic comparisons of each costed edge check. It takes the costed conjunction over all positions $v$ of: for a position of the odd player, the costed conjunction over all $w$ of "there is no move from $v$ to $w$, or the edge check succeeds"; for a position of the even player, the costed disjunction over all $w$ of "there is a move from $v$ to $w$ and the edge check succeeds". The same traversal computes the result and accumulates the cost.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
