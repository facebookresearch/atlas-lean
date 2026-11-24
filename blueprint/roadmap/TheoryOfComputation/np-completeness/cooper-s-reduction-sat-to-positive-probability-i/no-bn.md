# The fixed no-instance network

A rational Boolean network is a list of nodes in topological order, the last node being the output;
each node has a list of parents and a table of rows $(u, n, d)$ giving
$P(\text{node} = \text{true} \mid u) = n / d$ for the parents' values $u$. The fixed no-instance is
the network with one node: a parentless node that is true with probability $0$.
