# Running the vertex loop

Let $es$ be an edge list, $s, t, n$ numbers and $L$ a bound
with $n \le L$, $t \le L$ and at most $L$ bits in the encoding of $es$. For every list $q$ of
vertices whose witness encoding has at most $L$ bits, every count $c$, every previous vertex
$b \le L$ and every internal state, the verifier started at the vertex loop on the stack layout
between vertex steps for $es, s, t, n, c, b, q$ reaches within $(|q| + 1)(20L + 20)$ steps, with
some internal state and stacks, the accept label if the walk check for $s, t, n, es, c, b, q$
passes and the reject label otherwise.
