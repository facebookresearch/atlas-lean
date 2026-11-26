# Correctness and time bound of the 3-coloring verifier machine

Let $x$ and $w$ be
bit strings. Start the verifier machine at its start label, with any internal value, with $x$
written as bit symbols on the input stack $X$, $w$ written as bit symbols on the witness stack
$W$, and all other stacks empty. Then within at most $8(|x| + |w| + 1)^3$ steps it reaches the
accepting label if the [3-COLOR verifier](../part-06/col-check.md) accepts $(x, w)$, and the
rejecting label otherwise.
