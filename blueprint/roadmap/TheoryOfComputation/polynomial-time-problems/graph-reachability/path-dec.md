# The PATH problem

PATH is the decision problem that accepts a bit string $x$ exactly when
$x$ is the encoding of some instance $(s, t, n, E)$ with $s < n$, $t < n$ and a sequence
$s = v_0, v_1, \dots, v_k = t$ with $k \ge 0$ such that each $(v_i, v_{i+1})$ is an arc, that is,
a pair listed in $E$ with both ends below $n$.
