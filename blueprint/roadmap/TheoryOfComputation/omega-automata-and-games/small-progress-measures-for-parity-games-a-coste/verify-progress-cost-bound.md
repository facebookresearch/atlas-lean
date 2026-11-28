# Cost bound for the verifier

For $n$ positions and tuples of $d + 1$ numbers, the cost bound for the costed verifier is $n \cdot n \cdot (1 + B_d)$, where $B_d = (d+1)(2 + 2(d+1)) + 2(d+1)$: $n$ positions, each with at most $n$ successors, each pair costing one move test plus at most $B_d$ for the edge check.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
