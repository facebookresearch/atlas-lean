# Emulation constant

For a bundled multi-stack machine $M$, the emulation constant is
$C = 3(2B + 1) + P$, where $B = \sum_l |M(l)|$ is the total structural size of the statements
$M(l)$ over all labels $l$ (so each statement has size at most $B$), and $P$ is the push bound
of $M$, the total number of push instructions in its statements, which bounds the number of
pushes in one step.
