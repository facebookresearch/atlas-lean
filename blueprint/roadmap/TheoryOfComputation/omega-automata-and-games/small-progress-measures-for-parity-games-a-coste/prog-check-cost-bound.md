# Cost bound for one edge check

For $d \in \mathbb{N}$, the cost bound for one costed progress check is $(d + 1)(2 + 2(d + 1)) + 2(d + 1)$: the bound for the strict truncated comparison plus one scan of $d + 1$ indices with two atomic comparisons each for the non-strict case.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
