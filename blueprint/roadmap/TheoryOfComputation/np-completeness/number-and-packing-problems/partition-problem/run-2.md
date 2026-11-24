# Quadratic run of the raw-input SUBSET-SUM to PARTITION machine

For every bitstring $x$, the [raw-input machine](prog-2.md) started at $\mathsf{copy1}$ with
internal state false, with $x$ on $\mathit{raw}$ and every other stack empty, reaches
$\mathsf{done}$ in at most $60(|x| + 1)^2$ steps, with some internal state and stack contents in
which the padding machine's output stack $O$ holds the image of $x$ under the
[encoded reduction from SUBSET-SUM to PARTITION](reduce-from-subset-sum.md).

The bound is polynomial in the length of $x$, not in the numbers it encodes.
