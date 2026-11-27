# Decoding fails on a dangling half-pair

If reading a unary length prefix from a bit string
$x$ returns a number $u$ and the remaining suffix $r$, and reading a unary length prefix from $r$
fails, then the edge-list decoder fails on $x$.
