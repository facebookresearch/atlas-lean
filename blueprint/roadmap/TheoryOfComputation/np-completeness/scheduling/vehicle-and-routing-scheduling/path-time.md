# Travel time of a walk in the graph of the parent list

For an instance of VEHICLE SCHEDULING ON TREE and a walk $u = w_0, w_1, \dots, w_\ell = v$ in the [graph of its parent list](graph.md), the travel time of the walk is

$$\sum_{t=0}^{\ell - 1} \mathrm{travel}(w_t, w_{t+1}),$$

the sum of the travel times of its steps in the direction they are traversed.

The empty walk at a vertex has travel time $0$, also when the vertex is isolated.
