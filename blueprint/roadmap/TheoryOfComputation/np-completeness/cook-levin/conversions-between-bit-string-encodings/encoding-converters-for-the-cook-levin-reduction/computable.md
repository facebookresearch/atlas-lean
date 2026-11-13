# Canonical bit-list decoder

This is a multi-stack Turing machine over the alphabet
$\mathrm{Bool}$, with time bound $n + 2$, such that for every bit list $x$, started on the
canonical bitstring encoding of $x$, it halts within $n + 2$ steps, where $n$ is the length of
that encoding, with $x$ on its output stack and all other stacks empty. So the identity on bit
lists is computable in polynomial time from the canonical encoding to the raw bits.
