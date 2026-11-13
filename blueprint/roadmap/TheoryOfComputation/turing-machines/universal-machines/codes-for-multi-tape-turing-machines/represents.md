# Explicit configurations representing machine configurations

An explicit configuration $e$
represents a configuration $C$ of CSLib's multi-tape model on input $x$ when they have the same
state, the same shifted input head position and the same output, and for every work tape $i$ and
every cell $z \in \mathbb{Z}$, the content of cell $z$ of tape $i$ in $C$ equals the cell of tape
$i$ of $e$ at offset $z - p_i$ from its head, where $p_i$ is the head position of tape $i$
in $C$.
