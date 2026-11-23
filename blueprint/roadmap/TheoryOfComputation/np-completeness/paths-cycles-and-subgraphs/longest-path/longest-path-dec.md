# The LONGEST PATH decision problem

LONGEST PATH is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a longest-path
instance $(n, E, K, s, t)$ that is well formed and in which the graph of $E$ on $n$ vertices has
a simple path from $s$ to $t$ with at least $K$ edges. Bitstrings that do not decode to a
longest-path instance are rejected.
