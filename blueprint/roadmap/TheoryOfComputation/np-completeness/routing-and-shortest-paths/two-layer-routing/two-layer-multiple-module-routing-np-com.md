# TWO-LAYER MULTIPLE MODULE ROUTING is NP-complete

The TWO-LAYER MULTIPLE MODULE ROUTING decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a collection `{M₁, ..., Mₙ}` of non-intersecting modules (rectangles specified by their four integer-coordinate corners), a set `P` of terminals (grid points on the perimeters of the modules), a partition of `P` into nets `N₁, ..., Nₘ`, and an integer bound `B`. Question: is there a (reserved layer) routing for the nets that can be enclosed within a rectangle of area `B`, i.e., a set of grid segments `S = T₁ ∪ ... ∪ Tₘ` and a rectangle `R` such that (1) all the modules and all the grid segments in `S` are included in `R`, and none of the grid segments is contained in any of the modules, (2) for each `i`, the segments in `Tᵢ` make up a tree whose leaves are the points in net `Nᵢ`, and (3) no two trees `Tᵢ` and `Tⱼ` have any non-orthogonal intersections?

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [7] TWO-LAYER MULTIPLE MODULE ROUTING (reference: T. G. Szymanski, "Dogleg channel routing is NP-complete", manuscript (1982); transformation from 3SAT) and the reserved-layer model of Section 2.
