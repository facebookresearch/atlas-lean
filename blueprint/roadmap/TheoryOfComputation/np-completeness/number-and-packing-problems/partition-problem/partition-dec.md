# Binary-coded PARTITION decision problem

PARTITION is the decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the
canonical bitstring encoding of lists of natural numbers, to a
[feasible](partition-feasible.md) PARTITION instance; bitstrings that do not decode are rejected.
Decoding splits $x$ into blocks, each payload bit $c$ written as the two bits true, $c$ and each
block ended by a false bit, and fails unless $x$ is a concatenation of complete blocks; each
block's payload is read as a natural number in binary, least significant bit first, a nonempty
payload ending in false being read as if a final true bit followed it.
