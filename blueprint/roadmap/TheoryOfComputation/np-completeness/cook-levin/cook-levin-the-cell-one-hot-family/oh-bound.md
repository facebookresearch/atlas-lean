# Explicit time bound of the one-hot generator

For a layout $L$ and natural numbers $T$ and
$H$, the explicit time bound of the one-hot generator is $p + (T + 1)(b + 1) + (T + 1) + 2$,
where $p$ is the cost of its precomputation and $b$ the cost of one iteration of its time loop,
both for $L$, $T$ and $H$.

This bound is at most $668\,(A + K + g + 1)^7 (T + H + 1)^6$, where $A$ is the label block size,
$K$ the number of stacks and $g$ the number of symbol codes of $L$.
