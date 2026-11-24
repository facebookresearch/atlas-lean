# Joint law of a decoded rational network

A rational Boolean network is a list of nodes in topological order, the last node being the output;
each node has a list of parents and a table of rows $(u, n, d)$ giving
$P(\text{node} = \text{true} \mid u) = n / d$ for the parents' values $u$. Let the network be
well-formed: it is nonempty, and node $k$ has distinct parents below $k$, exactly one row for each
of the $2^{|\text{parents}|}$ parent values, and rows with $0 < d$ and $n \le d$. Decode it as a
Bayesian network over the reals whose node $k$ is true with probability given by its table. Then for
every assignment $x$ of Booleans to the nodes, the joint probability of $x$ equals the rational
product, over the nodes, of the table entry for the node's value given its parents' values under
$x$.
