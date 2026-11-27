# Correctness and running time of the edge loop

Let $cs$ be a list of color codes (pairs
of bits) and $r$ a list of bits, and encode an edge $(u, v)$ of natural numbers as $u$ ones, a
zero, $v$ ones and a zero. Call $r$ good for $cs$ when $r$ is a concatenation of encoded edges
such that, for every edge $(u, v)$ among them, $u$ and $v$ are below the length of $cs$ and, if
$u \ne v$, entries $u$ and $v$ of $cs$ (counting from $0$) differ. Suppose the 3-COLOR verifier
is at its edge label, in any internal state, with the input stack $X$ holding the bits of $r$
(first bit on top), the color stack $P$ holding the bits of the flattening of $cs$, the stacks
$T$, $U$ and $V$ empty, and the other stacks arbitrary. Then in at most $4|r| + 1$ steps it
reaches, in some internal state and with some stack contents, the accepting label if $r$ is good
for $cs$, and the rejecting label otherwise.
