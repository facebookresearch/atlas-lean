# An accepted input encodes an instance with a good vertex set

Fix a mode (clique,
independent set or vertex cover) and bit strings $x$ and $w$. If the verifier in that mode
accepts the input $x$ with witness $w$, then there are natural numbers $k$ and $n$ and a list of
bits $b$ such that $x$ is the encoding of the instance $(k, n, b)$, $b$ has exactly one bit per
vertex pair $(i, j)$ with $i < j < n$, and some set of exactly $k$ of the vertices
$0, \dots, n-1$ meets the mode's pair condition on every pair $i < j$.
