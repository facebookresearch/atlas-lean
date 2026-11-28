# The progress-measure verifier

For a parity game on $n$ positions and a partial assignment $\mu$ of tuples of $d + 1$ natural numbers to positions, the verifier accepts $\mu$ when at every position of the even player some successor $w$ satisfies the progress condition for the edge from $v$ to $w$, and at every position of the odd player every successor does. A position of the even player with no move therefore fails, and one of the odd player with no move passes.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
