# Feasible instances of STACKER-CRANE PATH

An instance of STACKER-CRANE PATH is feasible when there is a walk, given as a list `c` of indices into the moves of the STACKER-CRANE instance, in which each move starts where the previous one ends, every directed edge (index `< |A|`) occurs, and the total length is at most `B`. A walk has a start vertex even when it has no moves, so `V` is nonempty (`0 < n`). Feasibility does not include well-formedness; the decision problem requires both.
