# Canonical encoding of a pair of bit lists

For bit lists $x$ and $w$, the canonical
bitstring encoding of the pair $(x, w)$ is the concatenation of three parts: every bit $b$ of $x$,
in order, written as the six bits true, true, true, $b$, true, false; then a single false; then
every bit $b$ of $w$, in order, written as the three bits true, $b$, false.
