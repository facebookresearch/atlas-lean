# Kosaraju–Sharir block decomposition

Assume the vertex type has decidable equality and a Boolean equality test `==` that agrees with
equality and a hash function. For a directed graph given by adjacency lists, the Kosaraju–Sharir
decomposition runs a first depth-first pass over all vertices to get the decreasing finish order,
then a second depth-first pass on the transpose graph in that order; the blocks are the trees of the
second pass, listed by their preorder. The step counts proved for the two passes do not include the
cost of evaluating the adjacency functions.
