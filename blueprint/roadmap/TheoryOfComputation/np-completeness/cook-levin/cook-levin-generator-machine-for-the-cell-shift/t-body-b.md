# Step budget for one time step of the shift generator

Let $L$ be a layout with $K$
stacks, $g$ symbol codes and window depth $d$, let $N, T, H \in \mathbb{N}$, let $V = (T + 1) W$
be the number of variables, $W$ being the number of variables per time step at height $H$, and
let $B$ be the step budget for one block of the shift generator for $g$, $K$, $H$, $d$ and $V$.
The budget is

$$
\bigl(T(2V + 3) + T + 2\bigr) + (2V + 2) + (2V + 2) + N(K B) + (V + 1) + (V + 1).
$$
