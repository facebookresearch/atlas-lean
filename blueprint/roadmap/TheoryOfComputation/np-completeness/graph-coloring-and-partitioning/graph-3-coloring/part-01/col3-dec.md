# 3-COLOR

The decision problem 3-COLOR accepts a bit string $x$ exactly when there are a
natural number $n$ and a list $es$ of pairs of natural numbers such that $x$ is the encoding of
$n$ and $es$ ($n$ in unary, then each edge $(u, v)$ as $u$ and $v$ in unary), every edge
$(u, v)$ in $es$ has $u < n$ and $v < n$, and the graph on $\{0, \dots, n - 1\}$ with edge list
$es$ (symmetrized, loops dropped) is $3$-colorable.
