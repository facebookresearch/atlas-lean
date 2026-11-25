# 3-PARTITION as a decision problem

The decision problem 3-PARTITION accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a 3-partition instance
$(a, B)$ that is well formed (the length of the list $a$ is a multiple of $3$) and feasible (the
entries of $a$ can be split into triples each summing to $B$). Bitstrings that do not decode to
an instance are rejected.
