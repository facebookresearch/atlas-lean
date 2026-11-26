# PLS-Labyrinth gadget with bicubic interpolation: unavoidable KKT points at colour changes encode ITER solutions

In the construction of the staircase embedding, place at every point where a green and an orange path meet a **PLS-Labyrinth**: a region subdivided into exponentially many medium squares whose diagonal squares are indexed by the ITER nodes $u\in[2^m]$. The meeting point emits an *orange-blue path* to the medium square of node $1$; for each $u$ with $C(u)>u$ an orange-blue path runs from the adjacent orange path to the square of $u$, and if $u$ is not an ITER solution it continues as a *blue path* merging into the orange-blue path of $C(u)$. Sinks of orange-blue paths create $\varepsilon$-KKT points, sources of blue paths create none, so crossings are harmless.

Extend the grid data to all of $[0,N]^2$ by **bicubic interpolation** on each unit square from the prescribed values of $f$ and $\nabla f$ at its four corners. Then $f$ is continuously differentiable with $f$ and $\nabla f$ Lipschitz (constants $\mathrm{poly}(N)$ after scaling), circuits for $f$ and $\nabla f$ are well-behaved and of polynomial size, and every $\varepsilon$-KKT point inside a labyrinth lies in a unit square from which a node $u$ with $C(u)>u$ and $C(C(u))=C(u)$ is computable in polynomial time. The gadget works only at green/orange meeting points; placed elsewhere it would create easily located KKT points.

## Proof sketch

Bicubic interpolation produces on each unit square a polynomial matching values and gradients at the corners, so adjacent pieces agree to first order along shared edges and the glued function is $C^1$; on a compact grid of bounded-degree pieces both $f$ and $\nabla f$ are Lipschitz. The construction uses 101 distinct unit-square types (colour pattern and gradient directions at corners), and symmetries group them into four cases, in each of which one verifies directly that the interpolant has no $\varepsilon$-KKT point unless the square was designated to host a solution. Orange-blue sinks survive only at ITER solutions because every non-solution $u$ is rerouted into $C(u)$'s path.

## Depends on

- [Staircase embedding of END-OF-LINE into a planar descent landscape with green descending and orange ascending paths](staircase-embedding-green-orange-paths.md)
- [ITER and the EITHER-SOLUTION combinator for building PPAD ∩ PLS-complete problems](iter-and-either-solution.md)
- [Well-behaved arithmetic circuits and Lipschitz violation witnesses for continuous total search problems](well-behaved-arithmetic-circuits.md)
- [The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses](kkt-search-problem.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
