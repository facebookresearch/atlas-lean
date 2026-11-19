# Outer contour map: clusters as interiors of boundary circuits

For $n \in \mathbb{N}$, with $\Lambda_n = \{-n, \dots, n\}^2$, $B_n$ the nearest-neighbour bonds with at least one
endpoint in $\Lambda_n$ and the anchor sets $A_\ell = \{(j, 0), (j, -1) : 0 \le j < \ell\}$, this condition
holds when there is an [interior assignment](interior-assignment.md) $I$ such that for every spin
assignment $\tau$ on $\Lambda_n$ for which the configuration $\sigma_\tau$ equal to $\tau$ in $\Lambda_n$ and plus
outside is minus at the origin, there are $\ell \in \mathbb{N}$ and a simple cycle $\gamma$ of length $\ell$ based at
a site of $A_\ell$ such that

- the interior $I(\gamma)$ is contained in $\Lambda_n$,
- exactly $\ell$ bonds of $B_n$ have exactly one endpoint in $I(\gamma)$, and
- the [contour event](../contours-of-minus-clusters/contour-event.md) of $I(\gamma)$ for $B_n$ holds for
  $\sigma_\tau$.

The box and length conditions are required only of the cycles produced in this way: a cycle longer than
the number of bonds of $B_n$ cannot have an interior in $\Lambda_n$ with that many crossing bonds.
