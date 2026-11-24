# The single-tape machine of a code runs it step for step

If `c` has halted on `x` within
`T` steps, its single-tape machine halts on the input word of `x` within `T + 1` steps, the last
step entering its halting state, with a tape that reads as the tape of `c` after `T` steps.
