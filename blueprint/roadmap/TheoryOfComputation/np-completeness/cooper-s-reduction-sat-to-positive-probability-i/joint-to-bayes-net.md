# Joint law of a decoded rational network

A rational Boolean network is a list of nodes, whose last node, when there is one, is the output;
each node has a list of parent indices and a table of rows $(u, n, d)$, with $u$ a list of Booleans
and $n, d$ natural numbers. In general $n / d$ is only a rational table value; for a well-formed
network (nonempty, the parents of node $k$ distinct and below $k$, exactly one row for each parent
value, $0 < d$ and $n \le d$) it is the conditional probability $P(\text{node} = \text{true} \mid u)$
for the parents' values $u$. Let the network be well-formed, and decode it as a Bayesian network over the reals whose node $k$
is true with probability given by its table. Then for every assignment $x$ of Booleans to the nodes,
the joint probability of $x$ equals the real cast of the [rational joint](rat-joint.md): the product
over the nodes $k$ of $p_k$ if $x(k)$ is true and $1 - p_k$ if $x(k)$ is false, where $p_k$ is the
table entry of node $k$ read at its parents' values under $x$, in the order of its parent list.
