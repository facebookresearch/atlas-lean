# TWO-LAYER CHANNEL ROUTING is NP-complete

The TWO-LAYER CHANNEL ROUTING decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a positive integer `W`, a set of grid points `P = {(aᵢ, W) : 1 ≤ i ≤ p} ∪ {(bⱼ, 0) : 1 ≤ j ≤ q}`, and a partition of `P` into nets `N₁, ..., Nₘ`. Question: is there a (reserved layer) two-layer channel routing for the nets, i.e., a set of grid segments `S = T₁ ∪ ... ∪ Tₘ` where all the grid segments in `S` are included in the region between the lines `y = 0` and `y = W` (with none from those two lines), (2) for each `i`, the segments in `Tᵢ` make up a tree whose leaves are the points in net `Nᵢ`, and (3) no two trees `Tᵢ` and `Tⱼ` have any non-orthogonal intersections?

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [8] TWO-LAYER CHANNEL ROUTING (reference: Szymanski; transformation from 3SAT), with properties (2) and (3) from problem [7] TWO-LAYER MULTIPLE MODULE ROUTING and the reserved-layer model from Section 2.
- T. G. Szymanski, "Dogleg channel routing is NP-complete", IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 4 (1985), 31-41, doi:10.1109/TCAD.1985.1270096.
