# The SET SPLITTING decision problem

SET SPLITTING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a pair
$(n, C)$ of a natural number $n$ and a list $C$ of lists of natural numbers such that every list
in $C$ has no repeated entries and only entries less than $n$, and some finite set $S$ of natural
numbers less than $n$ contains an entry of every list in $C$ and misses an entry of every list in
$C$. Bitstrings that do not decode to such a pair are rejected.
