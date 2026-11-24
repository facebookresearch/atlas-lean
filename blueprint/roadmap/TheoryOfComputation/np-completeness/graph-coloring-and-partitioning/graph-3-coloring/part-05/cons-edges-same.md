# Consistency edges of two occurrences of the same variable

Let $x$, $L'$ and $n$ be
natural numbers and let $p$, $b$ be Booleans. The consistency edges between a new occurrence of
the literal $(x, p)$ with vertices $L = n$, $M = n + 1$ and an earlier occurrence
$(x, b, L', L' + 1)$ are $[(L', n + 1), (L' + 1, n)]$ if $b = p$, and
$[(L', n), (L' + 1, n + 1)]$ otherwise.
