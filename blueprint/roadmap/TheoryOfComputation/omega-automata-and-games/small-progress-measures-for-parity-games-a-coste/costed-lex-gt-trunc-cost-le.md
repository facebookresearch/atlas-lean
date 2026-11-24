# Costed Lex Gt Trunc cost le

The costed strict truncated order costs at most `(d + 1) * (2 + (d + 1) * 2)`:
for each of the `d + 1` candidate first-differing components, two atomic
comparisons plus one inner scan of `d + 1` pairs of atomic comparisons.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301.
