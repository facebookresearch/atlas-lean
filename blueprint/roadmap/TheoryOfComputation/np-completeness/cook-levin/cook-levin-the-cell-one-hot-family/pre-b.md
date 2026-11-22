# Step budget of the one-hot precomputation

For a layout with label/state block size $A$,
$K$ stacks and $g$ symbol codes, bounds $T$ and $H$, and row width $W = A + KHg$, the number of
steps allotted to the generator's precomputation is
$4 + (H(2g + 3) + H + 2) + (K(2Hg + 3) + K + 2) + ((T + 1)(2W + 3) + (T + 1) + 2)$.
