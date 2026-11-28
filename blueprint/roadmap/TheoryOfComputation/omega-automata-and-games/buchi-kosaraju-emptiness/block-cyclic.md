# Cyclic blocks

A directed graph is given by a duplicate-free list of all its vertices and, for each vertex, a list of its successors (its adjacency list); there is an edge from $s$ to $t$ when $t$ occurs in the adjacency list of $s$. A block, given as a list of vertices, is cyclic when it contains two distinct vertices or contains a vertex with an edge to itself. Distinctness matters: a list repeating one vertex twice has length $2$ but is cyclic only if that vertex has a self-loop.
