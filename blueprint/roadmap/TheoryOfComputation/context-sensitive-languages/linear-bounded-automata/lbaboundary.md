# Boundary tag of a linear bounded automaton head

A boundary tag is one of four values: middle (strictly inside the tape, neither the first nor the last
cell), left (the first cell of a tape of length at least two), right (the last cell of a tape of length
at least two), and both (the only cell of a one-cell tape). The transition function of a linear bounded
automaton reads the boundary tag of the head position, so the machine can tell the two ends of its tape
from interior cells.
