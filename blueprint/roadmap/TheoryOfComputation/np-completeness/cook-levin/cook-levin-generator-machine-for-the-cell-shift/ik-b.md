# Step budget for one block of the shift generator

For natural numbers $g$, $K$, $H$,
$d$ and $V$ (in use: the number of symbol codes, the number of stacks, the stack height, the
window depth and the number of variables), the budget is

$$
1 + (2V + 2) + 1 + \bigl(K(2V + 3) + K + 2\bigr) + (K + 1) + (2H + 2) + d + 1 +
\bigl((2V + 2) + (2V + 2) + d\,c(V) + (V + 1)\bigr) + \bigl(d\,(o + 1) + d + 2\bigr) +
\bigl(H\,(s + 1) + H + 2\bigr) + (H + 1) + (d + 1) + (V + 1),
$$

where $c(V)$ is the step budget of one clause, $o$ is the step budget $o(g, H, d, V)$ of one
iteration of the overflow loop, and $s$ is the step budget $s(g, H, V)$ of one iteration of
the in-range loop.
