# The marking algorithm for PATH

On a bit string $x$, the check decodes $x$ as a PATH
instance. If decoding fails it returns false; if it yields $(s, t, n, E)$ it returns true exactly
when $s < n$, $t < n$ and position $t$ of the marks after $n$ marking passes from $s$ over $E$
is true.
