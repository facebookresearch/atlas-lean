# The pass computes the Thompson state count of every node

For every list $l$ of nodes and
every index $k$, the entry at index $k$ of the state counts of $l$ (read as $0$ past the end of the
list) equals the Thompson state count of the regular expression at node $k$ of the encoding with
nodes $l$ when $k$ is less than the length of $l$, and $0$ otherwise.
