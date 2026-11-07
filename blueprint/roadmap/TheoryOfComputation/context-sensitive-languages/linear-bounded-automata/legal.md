# Legal head move of a linear bounded automaton

A move is legal from the head position `h` on a tape of length `n` when
the source head is on the tape and the new head position is still on the
tape. In particular a left move from an out-of-bounds head is illegal,
even though the truncated new head `h - 1` would still be out of bounds:
legality requires `h < n` for left moves as well.
