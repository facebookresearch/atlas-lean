# Cost bound for the costed cyclicity test

A directed graph is given by a duplicate-free list of all its vertices and, for each vertex, a list of its successors (its adjacency list); there is an edge from $s$ to $t$ when $t$ occurs in the adjacency list of $s$. The vertex type has decidable equality. The costed cyclicity test of a block costs at most $1$ plus the sum, over the vertices of the block, of the lengths of their adjacency lists.
