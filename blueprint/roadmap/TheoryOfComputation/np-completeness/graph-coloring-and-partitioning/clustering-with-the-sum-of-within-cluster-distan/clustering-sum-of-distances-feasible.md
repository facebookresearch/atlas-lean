# Feasible CLUSTERING with the sum of within-cluster distances instances

An instance $(D, K, B)$ in the CLUSTERING format is feasible for the sum-of-distances version when the $n$ elements can be assigned to parts $0, \dots, K-1$, every part receiving at least one element, so that $\sum_j \sum_{x, y \in X_j} d(x, y) \le B$, where $X_j$ is the set of elements in part $j$ and the inner sum runs over ordered pairs.
