# INDUCED SUBGRAPH ISOMORPHISM as a decision problem

The decision problem INDUCED SUBGRAPH
ISOMORPHISM accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance $(n, E, k, F)$ (host vertex count, host edge list, pattern vertex count,
pattern edge list) that is well-formed and for which there is an injective map $f$ from
$\{0, \dots, k - 1\}$ to $\{0, \dots, n - 1\}$ such that, for all $a$ and $b$, the vertices $a$
and $b$ are adjacent in the pattern graph if and only if $f(a)$ and $f(b)$ are adjacent in the
host graph. Bitstrings that do not decode to an instance are rejected.
