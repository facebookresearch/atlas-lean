# AND node of a rational Boolean network

A rational Boolean network is a list of nodes, whose last node, when there is one, is the output;
each node has a list of parent indices and a table of rows $(u, n, d)$, with $u$ a list of Booleans
and $n, d$ natural numbers. In general $n / d$ is only a rational table value; for a well-formed
network (nonempty, the parents of node $k$ distinct and below $k$, exactly one row for each parent
value, $0 < d$ and $n \le d$) it is the conditional probability $P(\text{node} = \text{true} \mid u)$
for the parents' values $u$. For node indices $i$ and
$j$, the AND node has parents $i, j$ and the deterministic table that is true with probability $1$
exactly when both parents are true and with probability $0$ otherwise.
