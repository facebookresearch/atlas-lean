# Length of a walk under edge lengths

Let $(n, E, C, K)$ be an instance and $w$ a list of natural numbers giving the $j$-th listed edge the length $w_j$. The length of a walk $p$ in the graph of the instance is the sum, over the edges $s$ traversed by $p$ (with multiplicity), of the length of $s$ under $w$ (the [edge length](edge-length.md): the $w_j$ of the first index $j < \min(|E|, |w|)$ with $e_j$ equal to $(a, b)$ or $(b, a)$, or $0$ if none).

The same sum gives the walk length for WEIGHTED DIAMETER with diameter $K$ or greater, and, summed over the steps of the walk in the order traversed, the walk length for WEIGHTED DIAMETER with diameter $K$ or less; each step contributes the length of its unordered endpoint pair, so the three readings agree on every walk, also for malformed lists.
