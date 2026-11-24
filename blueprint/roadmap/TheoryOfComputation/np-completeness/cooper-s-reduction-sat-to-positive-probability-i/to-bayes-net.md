# The decoded network as a Bayesian network over the reals

A rational Boolean network decodes to a Bayesian network over the reals with the same nodes. Node
$k$ has as parents its listed parents below $k$ and, given the parents' values $u$, the Bernoulli
distribution that is true with probability equal to the node's table entry for $u$, clamped to
$[0, 1]$. On a well-formed network the clamping changes nothing.
