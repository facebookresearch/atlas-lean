# Cooper's network is well-formed

A rational Boolean network is a list of nodes in topological order, the last node being the output;
each node has a list of parents and a table of rows $(u, n, d)$ giving
$P(\text{node} = \text{true} \mid u) = n / d$ for the parents' values $u$. For every CNF formula
$\varphi$, Cooper's network of $\varphi$ is well-formed: it is nonempty, and node $k$ has distinct
parents below $k$, exactly one row for each of the $2^{|\text{parents}|}$ parent values, and rows
with $0 < d$ and $n \le d$.
