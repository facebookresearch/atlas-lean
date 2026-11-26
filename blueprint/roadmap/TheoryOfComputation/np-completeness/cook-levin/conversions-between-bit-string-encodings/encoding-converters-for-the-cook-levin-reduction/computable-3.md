# Polynomial-time encoder to the canonical bit-list encoding

This is a multi-stack Turing
machine whose input and output alphabets are the bits, together with the polynomial time bound
$t(n) = 2n + 2$, such that for every bit list $x$ of length $n$, the machine started with $x$ on
its input stack and all other stacks empty halts within $t(n)$ steps with the canonical bitstring
encoding of $x$ on its output stack, all other stacks empty and its internal state back to the
initial one. So the identity on bit lists is computable in polynomial time from the raw bits to
the canonical encoding.

The canonical encoding writes each bit $b$ of $x$ as the three bits true, $b$, false.
