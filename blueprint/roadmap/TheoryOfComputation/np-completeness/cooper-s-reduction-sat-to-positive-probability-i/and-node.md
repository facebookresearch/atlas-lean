# AND node of a rational Boolean network

A rational Boolean network is a list of nodes in topological order, the last node being the output;
each node has a list of parents and a table of rows $(u, n, d)$ giving
$P(\text{node} = \text{true} \mid u) = n / d$ for the parents' values $u$. For node indices $i$ and
$j$, the AND node has parents $i, j$ and the deterministic table that is true with probability $1$
exactly when both parents are true and with probability $0$ otherwise.
