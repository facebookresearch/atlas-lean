# Pushed-fill forcing

Let $L$ be a layout with $A$ label/state variables, $K$ stacks and
$g$ symbol codes, let $\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ be situation tables and
$N, T, H \in \mathbb{N}$, and write $W = A + KHg$, $X[t, x] = tW + x$ and
$C[t, k, j, x] = tW + A + (kH + j)g + x$. If the assignment $a$ satisfies the cell-shift family
of these data, $t < T$, $i < N$, $k < K$, $j < \mathrm{pl}(i, k)$ and the variable
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$, then the variable
$C[t + 1, k, j, \mathrm{pu}(i, k, j)]$ is true under $a$.

Only the situation literal is read.
