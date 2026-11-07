# Walk step of the clique verifier

In mode $m$ with row flag $c$, the walk step looks at
the vertex stack $V$. If $V$ is empty, it moves to the accept label if the input stack $X$ is
empty and to the reject label otherwise. If $V$ is not empty, it pops the top symbol of $V$,
reads it as a bit $z$ (a non-bit symbol reads as false), and continues with the rest of the walk
step for $m$, $c$ and $z$.
