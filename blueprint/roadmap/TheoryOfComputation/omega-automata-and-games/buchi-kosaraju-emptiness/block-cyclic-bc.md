# Cyclicity test with cost counting

A directed graph is given by a duplicate-free list of all its vertices and, for each vertex, a list of its successors (its adjacency list); there is an edge from $s$ to $t$ when $t$ occurs in the adjacency list of $s$. The vertex type has decidable equality. The costed cyclicity test of a block returns true with cost $1$ if the block has length at least $2$; otherwise it runs the costed self-loop scan of the block and returns its answer with cost $1$ plus the number of adjacency entries the scan examined.
