# Finite-state doubling pass on raw bitstrings

The doubling pass from [phase](phase.md) $q$ maps the empty bitstring to the empty bitstring and
a bitstring $b x$ with first bit $b$ to the [output bits](chunk.md) for $b$ in phase $q$,
followed by the doubling pass of $x$ from the [next phase](next.md) of $q$ after $b$. It is
defined on every bitstring, whether or not it is a concatenation of blocks.
