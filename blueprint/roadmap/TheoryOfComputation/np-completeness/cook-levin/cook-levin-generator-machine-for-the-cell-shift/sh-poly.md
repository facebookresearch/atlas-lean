# The shift-generator time bound as a polynomial

For a layout $L$ with label/state block
size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, and a natural number $N$, let
$c = 828\,(A + K + g + d + N + 1)^7$ be the constant of the shift-generator time bound; this is
the polynomial $c\,(X + 1)^6$ with natural-number coefficients.

For natural numbers $T$ and $H$, its value at $X = T + H$ is $c\,(T + H + 1)^6$, the bound on
the number of steps of the shift generator started on $T$ and $H$.
