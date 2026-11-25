# Feasible instances of NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax

An instance of NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax is feasible when some no-wait open-shop schedule completes every operation of every job `j` by time `d_j + K`: each job's operations fill `m` consecutive unit slots, and the maximum lateness `max_j (C_j - d_j)` is at most `K`. Feasibility does not include well-formedness; the decision problem requires both. A position beyond the end of a list reads as the default entry `([], (0, 0))`.
