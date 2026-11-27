# Cooper's network is well-formed

A rational Boolean network is a list of nodes, whose last node, when there is one, is the output;
each node has a list of parent indices and a table of rows $(u, n, d)$, with $u$ a list of Booleans
and $n, d$ natural numbers. In general $n / d$ is only a rational table value; for a well-formed
network (nonempty, the parents of node $k$ distinct and below $k$, exactly one row for each parent
value, $0 < d$ and $n \le d$) it is the conditional probability $P(\text{node} = \text{true} \mid u)$
for the parents' values $u$. For every CNF formula
$\varphi$, Cooper's network of $\varphi$ is well-formed: it is nonempty, and node $k$ has distinct
parents below $k$, exactly one row for each of the $2^{|\text{parents}|}$ parent values, and rows
with $0 < d$ and $n \le d$.
