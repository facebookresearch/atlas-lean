# Threshold language of a counting function

For a function $f$ from bitstrings to
natural numbers, the threshold language of $f$ is the decision problem that accepts a bitstring
$y$ exactly when decoding $y$ with the canonical bitstring encoding of pairs of a bitstring and
a natural number succeeds and gives a pair $(x, k)$ with $k \le f(x)$; bitstrings that do not
decode are rejected.
