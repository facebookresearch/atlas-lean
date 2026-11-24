# Step counts of the two depth-first passes of Kosaraju–Sharir

Assume the vertex type has decidable equality and a Boolean equality test `==` that agrees with
equality and a hash function. For a directed graph with $V$ vertices whose adjacency lists have
total length $E$, the first depth-first pass of the Kosaraju–Sharir decomposition reaches its final
state, with empty work list and the whole-graph finish order, in exactly $2V + E$ machine steps. The
second pass, on the transpose graph in decreasing finish order, reaches its final state in exactly
$R + P + E_2$ steps, where $R$ is the length of that order, $P$ the length of the second pass's
preorder and $E_2$ the total length of the transpose adjacency lists over that preorder. These are
counts of abstract machine steps; they do not include the cost of evaluating the adjacency
functions.
