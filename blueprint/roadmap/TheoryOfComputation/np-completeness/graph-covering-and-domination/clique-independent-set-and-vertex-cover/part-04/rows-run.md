# All rows of the clique verifier's walk

Let $m$ be a mode, $r$ and $b$ lists of
bits, $v$ a state and $S$ stack contents in which the vertex stack $V$ holds, from the top,
the bits of the reverse of $r$ (so the last entry of $r$ is on top), the scratch stack $T$
is empty, and the input stack $X$ holds the bits $b$. Then there are a state $v'$ and stack
contents $S'$ such that within at most $|r|(2|r| + 2) + 1$ steps the verifier program of
mode $m$ goes from label walk(true) with state $v$ and stacks $S$ to state $v'$ and stacks
$S'$ at the accepting label if the row-by-row check of $r$ against $b$ holds for $m$, and
at the rejecting label otherwise.
