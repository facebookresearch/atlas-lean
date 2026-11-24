# 3-DIMENSIONAL MATCHING as a decision problem

The decision problem 3-DIMENSIONAL MATCHING
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
3-dimensional matching instance $(n, T)$ that is well formed (every coordinate of every triple in
$T$ is less than $n$) and feasible (it has a perfect matching). Bitstrings that do not decode to
an instance are rejected.
