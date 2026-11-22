# Raw-input PARTITION membership machine runs in quadratic time

For every bitstring $x$, the [raw-input membership machine](prog-4.md) started at the normalizer's
label $\mathsf{loop}$ with internal state false, with $x$ on the normalizer's input stack and
every other stack empty, reaches $\mathsf{done}$ in at most $100(|x| + 1)^2$ steps, with some
internal state and stack contents in which the doubling machine's output stack $O$ holds the image
of $x$ under the [encoded reduction from PARTITION to SUBSET-SUM](reduce-to-subset-sum.md). This
covers bitstrings that do not decode and those that decode only with a noncanonical payload.
