# The diagonal language through the universal machine

For every time bound
$f : \mathbb{N} \to \mathbb{N}$ and every code $c$ with code stack $x$, the bit list $x$ belongs to
the diagonal language for $f$ iff the output encoding of the result of running $c$ on $x$ for at
most $f(|x|)$ steps differs from the output encoding of the result whose output is the single
symbol $2$ of the bit true.

The clocked universal machine reads the input encoding of a code, an input and a clock $T$ and
writes the output encoding of the result of running the code on the input for at most $T$ steps,
so the condition is read from its output on $c$, $x$ and $f(|x|)$.
