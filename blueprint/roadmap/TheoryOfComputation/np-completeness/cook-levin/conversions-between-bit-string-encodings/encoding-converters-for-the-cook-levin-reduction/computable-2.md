# Polynomial-time decoder of the canonical bit-list encoding

This is a multi-stack Turing
machine whose input and output alphabets are the bits, together with the polynomial time bound
$t(n) = n + 2$, such that for every bit list $x$, whose canonical bitstring encoding has length
$n$, the machine started with that encoding on its input stack and all other stacks empty halts
within $t(n)$ steps with $x$ on its output stack, all other stacks empty and its internal state
back to the initial one. So the identity on bit lists is computable in polynomial time from the
canonical encoding to the raw bits.

The canonical encoding writes each bit $b$ of $x$ as the three bits true, $b$, false.
