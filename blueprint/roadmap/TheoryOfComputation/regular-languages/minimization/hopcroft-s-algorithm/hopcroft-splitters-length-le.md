# The splitter trace records exactly the splitters the loop pops

The loop and the
trace recurse on the same state, so they take the same number of steps. The two
theorems below make the correspondence usable: the trace length is at most `k`, and
running the loop for exactly the trace's length gives the full loop result, so the trace
contains every splitter the loop pops and no others.
