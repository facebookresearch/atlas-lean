# Cost bound for the self-loop scan

A directed graph is given by a duplicate-free list of all its vertices and, for each vertex, a list of its successors (its adjacency list); there is an edge from $s$ to $t$ when $t$ occurs in the adjacency list of $s$. The vertex type has decidable equality. The costed self-loop scan of a block examines adjacency-list entries one by one, looking for a vertex of the block in its own adjacency list. The number of entries it examines is at most the sum, over the vertices of the block, of the lengths of their adjacency lists.
