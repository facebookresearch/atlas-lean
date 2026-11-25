# Feasible FAULT DETECTION WITH TEST POINTS instances

A FAULT DETECTION WITH TEST POINTS instance is feasible when some set `A'` of at most `K` arcs
makes the test set `T = ({s} ∪ {tails of A'}) × ({t} ∪ {heads of A'})` locate every single
fault: for all distinct `v, v' ∉ {s, t}` some `(u₁, u₂) ∈ T` has `v` on a directed path from
`u₁` to `u₂` and `v'` on no such path.
