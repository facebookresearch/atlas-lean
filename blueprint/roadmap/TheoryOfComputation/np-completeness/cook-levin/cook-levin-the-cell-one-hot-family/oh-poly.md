# The one-hot time bound as a polynomial

For a layout with label/state block size $A$, $K$
stacks and $g$ symbol codes, let $c = 668\,(A + K + g + 1)^7$; this is the polynomial
$c\,(X + 1)^6$ with natural-number coefficients. For natural numbers $T$ and $H$, its value at
$X = T + H$ is $c\,(T + H + 1)^6$, the bound on the number of steps of the one-hot generator
started on $T$ and $H$.
