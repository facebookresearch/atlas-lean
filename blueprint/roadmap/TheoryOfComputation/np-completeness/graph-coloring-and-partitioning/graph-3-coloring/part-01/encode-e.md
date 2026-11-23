# Bit-string encoding of a graph

The graph encoding of a number $n$ and a list $E$ of pairs
of natural numbers is the bit string that writes $n$ in unary and then, for each pair $(u, v)$
of $E$ in order, writes $u$ and then $v$ in unary, where a natural number $k$ is written in
unary as $k$ ones followed by one zero.
