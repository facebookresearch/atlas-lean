# The SHORTEST COMMON SUPERSEQUENCE decision problem

SHORTEST COMMON SUPERSEQUENCE is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to a pair $(R, K)$ of a list $R$ of lists of booleans and a natural number
$K$ for which some list of booleans of length at most $K$ has every list in $R$ as a subsequence.
Bitstrings that do not decode to such a pair are rejected.
