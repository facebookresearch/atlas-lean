# Per-literal time bound of the transition-clause generator

For a layout with label/state
block size $A$, $K$ stacks and $g$ symbol codes, and for $T, H \in \mathbb{N}$, let
$W = A + KHg$ be the number of variables per time step and $V = (T + 1)W$ the number of
variables. The per-literal time bound is $6V + K(2Hg + 3) + 2K + 2W + 22$.

It bounds the steps spent on one literal apart from the loop that emits the gap before it.
