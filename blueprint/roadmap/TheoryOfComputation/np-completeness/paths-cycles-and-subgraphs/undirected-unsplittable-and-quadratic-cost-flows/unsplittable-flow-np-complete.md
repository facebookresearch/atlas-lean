# UNSPLITTABLE FLOW is NP-complete

The [decision problem](unsplittable-flow-dec.md) UNSPLITTABLE FLOW belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: with $K = 1$ the question is the single-source unsplittable flow problem itself, choosing one path for each demand so that the capacities are respected, which the cited work proves NP-hard.

## Sources

- J. M. Kleinberg, "Single-source unsplittable flow", in *Proceedings of the 37th Annual Symposium on Foundations of Computer Science*, IEEE (1996), 68-77, doi:10.1109/SFCS.1996.548465 (the single-source unsplittable flow problem, "a natural, NP-hard generalization" of the single-source disjoint paths problem).
- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem MINIMUM UNSPLITTABLE FLOW.
