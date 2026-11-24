# Flattening blocks of bits

For $n > 0$ and $k$ blocks $x_0, \dots, x_{k-1}$ of $n$ bits
each, the flattened string has $nk$ bits, and its bit $i$ is bit $i \bmod n$ of the block
$x_{\lfloor i/n \rfloor}$.
