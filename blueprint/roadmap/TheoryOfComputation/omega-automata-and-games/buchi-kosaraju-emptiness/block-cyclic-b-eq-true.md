# The Boolean cyclicity test is correct on duplicate-free blocks

Call a list of vertices of a directed graph cyclic when it contains two distinct vertices or a
vertex with a self-loop. Assume equality on the vertex type is decidable, and let the Boolean test
return true exactly when the list has length at least two or contains a vertex with a self-loop. For
every duplicate-free list of vertices, the test returns true if and only if the list is cyclic.
Without the duplicate-free hypothesis the list $[s, s]$ would pass the length test with no
self-loop.
