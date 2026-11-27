# Next walking label

Write $w_i$ for the walking label after $i$ literals of the current
clause ($w_3$: three or more). For a Boolean $c$ (whether the filter is capped), the label after
one more literal sends $w_0$ to $w_1$, $w_1$ to $w_2$ and $w_2$ to $w_3$; it sends $w_3$ to the
failure label when $c$ is true and to $w_3$ when $c$ is false; every other label is unchanged.
