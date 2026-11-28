# Cost bound for the costed strict truncated comparison

For a threshold $p$ and tuples $a, b$ of $d + 1$ natural numbers, the costed strict truncated comparison costs at most $(d + 1)(2 + 2(d + 1))$: for each of the $d + 1$ candidate indices $j$, two atomic comparisons plus one scan of $d + 1$ indices with two atomic comparisons each.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
