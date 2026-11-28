# Borda score in POSSIBLE WINNER for Borda

In POSSIBLE WINNER for Borda: the Borda score of `a` when each voter `v` casts the linear order `P v`: the sum over the votes of `m - 1 - (position of a)`, for `m = |C|` alternatives, computed with truncated subtraction. The position of an alternative missing from a vote is that vote's length, so with `m = 3` alternatives an empty vote contributes `3 - 1 - 0 = 2`; that every vote is a permutation of the alternatives is a separate condition.
