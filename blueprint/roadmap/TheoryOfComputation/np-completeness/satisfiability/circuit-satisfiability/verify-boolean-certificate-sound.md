# Soundness of the Boolean certificate verifier

Let $c$ be a circuit over the Boolean
signature with $n$ inputs, $s$ gates and one output, and let $b = (b_0, \dots, b_{m-1})$ be an array
of truth values, where an entry at a position at or beyond $m$ is read as false and the position
of a wire is $k$ for input $k$ and $n + j$ for gate $j$. If the Boolean certificate verifier
accepts $b$, then, writing $x = (b_0, \dots, b_{n-1})$, the value of every wire of $c$ on input $x$
under the Boolean interpretation equals the entry of $b$ at the position of that wire, and the
output of $c$ on input $x$ is true.
