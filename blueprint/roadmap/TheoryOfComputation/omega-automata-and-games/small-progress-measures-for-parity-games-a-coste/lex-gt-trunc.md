# Lex Gt Trunc

The strict truncated lexicographic order at priority `p`: `a >_p b`
iff, scanning components from `d` down to `p`, the first component where
`a` and `b` differ has `a` strictly larger. Components below `p` are
ignored. Source: M. Jurdziński, "Small progress measures for solving parity
games", *Proceedings of STACS 2000*, LNCS 1770, 290-301.
