# Precomputation stages of the shift generator

The labels of the precomputation that the
cell-shift generator runs before its time loop: six plain stages and three multiplication sites,
each of the latter tagged with a stage of the multiplication routine. For a layout with $A$ label
variables, $K$ stacks and $g$ symbol codes, and the inputs $T$ (number of time steps) and $H$
(height), in order of execution they set a counter $G$ to $g$; set a counter $HG$ to $H g$ (a
multiplication site); set the row-width counter $W$ to $A$; set a scratch counter to $K$; add
$K \cdot HG$ to $W$ (a multiplication site), so that $W = A + K H g$; empty the scratch counter;
set the variable counter $V$ to $T W$ (a multiplication site); and add $W$ to $V$ in two copy
steps, so that $V = (T + 1) W$.
