# The final marks are exactly the reachable vertices

Let $n, s, t \in \mathbb{N}$ with
$s < n$ and $t < n$, and let $E$ be a list of pairs of natural numbers. Start from the marks on
$0, \dots, n - 1$ in which only $s$ is marked and apply $n$ marking passes of $E$ with bound $n$.
Then $t$ is marked if and only if $t$ is reachable from $s$ in zero or more steps along the arcs
of $E$ below $n$, the pairs $(u, v) \in E$ with $u < n$ and $v < n$.
