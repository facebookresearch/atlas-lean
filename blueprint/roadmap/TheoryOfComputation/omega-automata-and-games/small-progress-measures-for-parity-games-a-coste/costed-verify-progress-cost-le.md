# Cost bound for the costed progress-measure verifier

For a parity game on $n$ positions and a partial assignment $\mu$ of tuples of $d + 1$ natural numbers to positions, the costed progress-measure verifier costs at most $n \cdot n \cdot (1 + B_d)$, where $B_d = (d+1)(2 + 2(d+1)) + 2(d+1)$ bounds the cost of one edge check. This is a polynomial in $n + d$; on a game whose priorities are compressed to $d = 2n$ it is of order $n^4$.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
