# Each non-edge contributes a factor 2 to the partition function

Let $G$ be a simple graph on a finite set $V$ and $p, q \in \mathbb{R}$. Then

$$Z_G(p, q) = 2^{M} Z^{e}_G(p, q),$$

where $Z_G$ is the [random-cluster partition function](../random-cluster-measures-on-finite-graphs/fk-z.md) (summing the weights over all assignments of states to the unordered pairs of elements of $V$), $M$ is the [number of unordered pairs that are not edges of $G$](ecz-ne.md) (loops included), and $Z^{e}_G(p, q)$ is the [edge partition function](ecz-fk-zedge.md) (the sum of the random-cluster weights over the configurations closed on every pair that is not an edge of $G$).
