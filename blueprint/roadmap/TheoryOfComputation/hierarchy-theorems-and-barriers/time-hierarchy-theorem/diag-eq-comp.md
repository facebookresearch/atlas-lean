# The diagonal language through the clocked evaluator

For every
$f : \mathbb{N} \to \mathbb{N}$ and every bit list $x$, let $(c, y, T)$ be the universal machine's
argument for the diagonal language of $f$ on $x$. Then the diagonal language of $f$ holds at $x$
iff the clocked evaluator, running $c$ on $y$ for at most $T$ steps, does not return the output
$[2]$, the symbol of the answer true.
