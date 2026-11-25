# SCHEDULING WITH INDIVIDUAL DEADLINES for out-tree precedence is NP-complete

The SCHEDULING WITH INDIVIDUAL DEADLINES for out-tree precedence decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors, a partial order `<` on `T` that is an "out-tree" partial order (no task has more than one immediate predecessor), and for each task `t ∈ T` a deadline `d(t) ∈ ℤ⁺`. Question: is there an `m`-processor schedule `σ` for `T` that obeys the precedence constraints and meets all the deadlines, i.e., `σ(t) + l(t) ≤ d(t)` for all `t ∈ T`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS11] SCHEDULING WITH INDIVIDUAL DEADLINES, comment: remains NP-complete even if `<` is an "out-tree" partial order (no task has more than one immediate predecessor).
- P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2 (1977), 275-284, doi:10.1287/moor.2.3.275.
