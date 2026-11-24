# The network decoder inverts the encoding

A rational Boolean network is a list of nodes in topological order, the last node being the output;
each node has a list of parents and a table of rows $(u, n, d)$ giving
$P(\text{node} = \text{true} \mid u) = n / d$ for the parents' values $u$. For every rational
Boolean network $r$, decoding the bit-string encoding of $r$ returns $r$.
