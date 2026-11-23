# Ordered graphs for first-order logic with transitive closure

An ordered graph is
encoded as a pair $(n, e)$ of a natural number $n$, the domain size, and a finite list $e$ of
booleans of arbitrary length, the edge table in row-major order. It is read as the graph on
$\{0, \dots, n - 1\}$, ordered numerically, with an edge from $a$ to $b$ when the entry of $e$ at
position $an + b$ is true; a missing entry counts as false.
