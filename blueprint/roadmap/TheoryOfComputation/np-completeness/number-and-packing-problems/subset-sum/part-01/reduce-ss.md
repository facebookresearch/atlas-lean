# Reduction from VERTEX-COVER to SUBSET-SUM

The map on bit strings reads $x$ as $k$ ones, a
zero, $n$ ones, a zero and a remaining list $b$ of pair bits. If this parse succeeds and $b$ has
exactly $n(n-1)/2$ bits, one per vertex pair, then $x$ is sent to the encoding of the SUBSET-SUM
instance whose numbers are the numbers of the reduction for $n$ and $b$ and whose target is the
target for $k$, $n$ and $b$. Otherwise $x$ is sent to the fixed no-instance with no numbers and
target $1$.
