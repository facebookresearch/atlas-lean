# Unary reader of the 3-COLOR verifier

Given a counter stack $c$ and labels $s$ (its own)
and $t$ (the next): if the input stack $X$ is empty, reject; otherwise pop a bit off $X$; if it
is $1$, push a unit onto $c$ and go back to $s$, and if it is $0$, go to $t$. A symbol of $X$
that is not a bit is read as $0$.
