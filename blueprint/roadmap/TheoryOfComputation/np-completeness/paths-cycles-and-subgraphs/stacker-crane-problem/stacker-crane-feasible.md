# Feasible instances of STACKER-CRANE

An instance of STACKER-CRANE is feasible when there is a closed walk, given as a list `c` of indices into `moves i`, in which consecutive moves (cyclically) share an endpoint, every directed edge (index `< |A|`) occurs, and the total length is at most `B`. Feasibility does not include well-formedness; the decision problem requires both.
