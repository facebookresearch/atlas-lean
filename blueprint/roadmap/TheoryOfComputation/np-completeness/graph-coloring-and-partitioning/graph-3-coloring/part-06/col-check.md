# The 3-COLOR verifier

The verifier accepts an input $x$ and a witness $w$ (bit strings)
iff $x$ decodes to a number $n$ and an edge list $E$, every endpoint of an edge in $E$ is less
than $n$, $w$ has at least $2n$ bits, every vertex $i < n$ has a valid color code in $w$ (bits
$2i$ and $2i + 1$, not $11$), and the two ends of every edge $(u, v) \in E$ with $u \ne v$ have
different color codes.
