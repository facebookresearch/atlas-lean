# The outer contour map exists in every box

For every $n \in \mathbb{N}$, the [outer contour map condition](../outer-contours-on-the-square-lattice/outer-contour-map.md)
holds in $\Lambda_n = \{-n, \dots, n\}^2$. Read the sites of a closed walk as faces of $\mathbb{Z}^2$, each labelled
by its lower-left corner, so that each step of the walk crosses a lattice edge. A witnessing interior assignment
sends a closed walk to the connected set in $\Lambda_n$ containing the origin whose crossing bonds (the bonds
touching $\Lambda_n$ with exactly one endpoint in the set) are exactly the lattice edges the walk crosses, when
there is such a set (it is then unique), and to the empty set otherwise. Each configuration with the origin minus
is sent to a simple cycle through the whole contour of its [filled](spin-compatible-fill.md) minus cluster, based
at a site $(j, 0)$ with $j \in \mathbb{N}$ less than the contour length, and the interior of that cycle is the
filled cluster.
