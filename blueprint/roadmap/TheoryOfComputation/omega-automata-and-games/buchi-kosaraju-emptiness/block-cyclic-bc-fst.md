# The costed cyclicity test gives the Boolean test

A directed graph is given by a duplicate-free list of all its vertices and, for each vertex, a list of its successors (its adjacency list); there is an edge from $s$ to $t$ when $t$ occurs in the adjacency list of $s$. The vertex type has decidable equality. The costed cyclicity test of a block returns the same Boolean as the plain cyclicity test: true exactly when the block has length at least $2$ or some vertex of it has an edge to itself.
