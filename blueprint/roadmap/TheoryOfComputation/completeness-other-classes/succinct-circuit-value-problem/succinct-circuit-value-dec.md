# Succinct Circuit Value

The decision problem Succinct Circuit Value accepts a bitstring
exactly when it decodes to a triple $(n, C, x)$ of a natural number $n$, a list $C$ of encoded
gates and a bitstring $x$ such that: $x$ has length $n$; $C$ has at least $2n + 3$ gates and,
read as a flat Boolean circuit on $n$ inputs, is well formed; the circuit $D$ with $2^n$ gates
succinctly described by $C$, whose gate $i$ is described by the outputs of $C$ on the $n$-bit
binary expansion of $i$, is well formed; and the last gate of $D$ outputs true when the first
$n$ gates of $D$ are fed the bits of $x$.
