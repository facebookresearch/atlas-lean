# Decoding one pair, then the rest

If reading a unary length prefix from a bit string $x$
returns $u$ with remaining suffix $r$, and reading one from $r$ returns $v$ with remaining suffix
$r'$, then the edge-list decoder succeeds on $x$ exactly when it succeeds on $r'$, and in that
case its result on $x$ is its result on $r'$ with the pair $(u, v)$ put in front.
