# Index of a cell variable in the transition-family layout

For a layout $L$ with
label/state block size $A$, $K$ stacks and $g$ symbol codes, and natural numbers $H$, $t$, $k$,
$j$, $x$, the variable for stack $k$, depth $j$ from the top and symbol code $x$ at time $t$ has
index $tW + A + (kH + j)g + x$, where $W = A + KHg$ is the number of variables per time step. It is
meant for $k < K$, $j < H$ and $x < g$ but is defined for all values.
