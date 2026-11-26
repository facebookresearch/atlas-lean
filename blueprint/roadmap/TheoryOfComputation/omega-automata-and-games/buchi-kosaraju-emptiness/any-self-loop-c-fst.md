# The costed self-loop scan gives the right answer

A directed graph is given by a duplicate-free list of all its vertices and, for each vertex, a list of its successors (its adjacency list); there is an edge from $s$ to $t$ when $t$ occurs in the adjacency list of $s$. The vertex type has decidable equality. The costed self-loop scan of a block returns true exactly when some vertex of the block has an edge to itself.
