# Graph of a candidate edge set

Given a Steiner tree instance with vertex count $n$ and a
list $T$ of triples $(u, v, w)$ of natural numbers, the graph of $T$ is the simple graph on
$\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j, w)$ or
$(j, i, w)$ belongs to $T$ for some natural number $w$. Weights are ignored, and triples with an
endpoint at least $n$ contribute no edge.
