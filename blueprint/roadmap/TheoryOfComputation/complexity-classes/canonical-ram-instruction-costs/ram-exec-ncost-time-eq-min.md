# The time cost of a budgeted RAM run is the budget capped at the halting step

Let a RAM program, started from a state $s$, keep its program counter inside the program for the
first $h$ steps (for every $k < h$) and have it at or past the end of the program after $h$ steps.
Then for every budget $B$, the costed run of at most $B$ steps from $s$ has time cost $\min(B, h)$,
with zero cumulative space and zero peak memory. The case $h = 0$ covers empty programs and states
that have already halted.
